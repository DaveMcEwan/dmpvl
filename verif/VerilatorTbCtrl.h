#ifndef _VERILATORTBCTRL_H
#define _VERILATORTBCTRL_H

#include <fcntl.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>

#include "verilated.h"
#include "verilated_vcd_c.h"

#include "dmpvlCommon.h"

#define TBCTRL_BUFLEN 32
#define TBCTRL_FIFOPATH "tbCtrl"

template <class VA> class VerilatorTbCtrl { // {{{
public:
  VA*               m_dut;
  VerilatedVcdC*    m_trace;
  uint64_t          m_tickcount;
  int               m_ctrlfifo;
  bool              m_doDump;
  int               m_doStep;
  struct timespec   m_tickRqtp;

  VerilatorTbCtrl(const char* vcdname) : m_trace(NULL), m_tickcount(0l) {
    VERB("Enter");
    m_dut = new VA;
    Verilated::traceEverOn(true);
    m_dut->i_clk = 0;
    m_dut->i_rst = 1;
    m_doDump = true;
    m_doStep = 0;
    m_tickRqtp.tv_sec = 0;
    m_tickRqtp.tv_nsec = (long int)1E8; // 10Hz
    eval(); // Get our initial values set properly.
    opentrace(vcdname);
    openctrl();
    VERB("  Exit");
  }

  virtual ~VerilatorTbCtrl(void) {
    VERB("Enter");
    closetrace();
    closectrl();
    delete m_dut;
    m_dut = NULL;
    VERB("  Exit");
  }

  virtual void openctrl(void) {
    VERB("Enter path=%s", TBCTRL_FIFOPATH);

    // Delete any pre-existing named pipe.
    remove(TBCTRL_FIFOPATH);

    if (0 > mkfifo(TBCTRL_FIFOPATH, 0666)) {
      ERROR("Cannot open control fifo.");
    }

    m_ctrlfifo = open(TBCTRL_FIFOPATH, O_RDONLY | O_NONBLOCK);
    VERB("  m_ctrlfifo: %d", m_ctrlfifo);
    VERB("  Exit");
  }

  virtual void closectrl(void) {
    VERB("Enter");
    if (0 <= m_ctrlfifo) {
      close(m_ctrlfifo);
    }
    remove(TBCTRL_FIFOPATH);
    VERB("  Exit");
  }

  virtual void opentrace(const char* vcdname) {
    VERB("Enter");
    if (!m_trace) {
      VERB("  VCD path=%s", vcdname);
      m_trace = new VerilatedVcdC;
      m_dut->trace(m_trace, 99);
      m_trace->open(vcdname);
    }
    VERB("  Exit");
  }

  virtual void closetrace(void) {
    VERB("Enter");
    if (m_trace) {
      VERB("  Closing trace VCD");
      m_trace->close();
      delete m_trace;
      m_trace = NULL;
    }
    VERB("  Exit");
  }

  virtual void eval(void) {
    m_dut->eval();
  }

  // Call from loop {check, drive, tick}
  virtual void tick(void) {
    VERB("Enter tickcount=%d", m_tickcount);

    struct timespec walltime;
    if (0 != clock_gettime(CLOCK_REALTIME, &walltime)) {
      ERROR("Cannot get walltime.");
    }
    VERB("  walltime={%lld %09ld}", walltime.tv_sec, walltime.tv_nsec);

    VERB("  posedge");
    m_dut->i_clk = 1;
    m_dut->eval();
    if (m_doDump && m_trace) {
      m_trace->dump((uint64_t)(10*m_tickcount));
    }

    VERB("  negedge");
    m_dut->i_clk = 0;
    m_dut->eval();
    if (m_doDump && m_trace) {
      m_trace->dump((uint64_t)(10*m_tickcount+5));
      m_trace->flush();
    }

    m_tickcount++;
    VERB("  Exit");
  }

  virtual void reset(void) {
    VERB("Enter");
    m_dut->i_rst = 1;
    for (int i = 0; i < 5; i++)
      tick();
    m_dut->i_rst = 0;
    VERB("  Exit");
  }

  unsigned long tickcount(void) {
    return m_tickcount;
  }

  virtual bool done(void) {
    return Verilated::gotFinish();
  }

  virtual char* readCtrlLine(void) {
    static int i = 0;
    static char buf[TBCTRL_BUFLEN] = {0};

    char* ret_line      = buf;
    char* ret_error     = (char*)(-1);
    char* ret_notReady  = (char*)(NULL);

    int nRead;
    char* ret;

    while (1) {
      // https://linux.die.net/man/2/read
      if (0 > (nRead = read(m_ctrlfifo, &buf[i], 1))) {
        // Cannot get char either because there's no data in fifo, or an error.
        bool blocking = (EAGAIN == errno) || (EWOULDBLOCK == errno);
        if (blocking) errno = 0;
        ret = blocking ? ret_notReady : ret_error;
        break;
      }

      if (0 == nRead) {
        ret = ret_notReady;
        break;
      }

      // Zero characters read, without causing an error.
      assert(1 == nRead);

      if (buf[i] == '\n') {
        // End of line --> return pointer to buf.

        buf[i] = '\0'; // Avoid comparisons with command separator.
        i = 0;

        ret = ret_line;
        break;
      }

      if (i > TBCTRL_BUFLEN-1) {
        // No space left in buffer --> return error
        i = 0;
        ret = ret_error;
        break;
      }

      // Read another character into buffer, now try to get another.
      i++;
    }

    return ret;
  }

  virtual bool strStartswith(const char* prefix, const char* str) {
    return (0 == strncmp(prefix, str, strlen(prefix)));
  }

  virtual bool strEqualto(const char* cmp, const char* str) {
    return (0 == strncmp(cmp, str, TBCTRL_BUFLEN));
  }

  virtual void setPeriodNsec(uint64_t period_ns) {
    double frequency_Hz = 1E9/period_ns;

    m_tickRqtp.tv_sec = (long int)period_ns / (uint64_t)1E9;
    m_tickRqtp.tv_nsec = (long int)period_ns % (uint64_t)1E9;

    VERB("  Frequency=%fHz Period=%dns", frequency_Hz, period_ns);
  }

  virtual void run(int maxNCycles) {
    char* cmd;

    VERB("Enter maxNCycles=%d", maxNCycles);

    while (tickcount() < maxNCycles) {
      if (0 != clock_nanosleep(CLOCK_REALTIME, 0, &m_tickRqtp, NULL)) {
        printf("errno=%d");
        ERROR("sleep failed.");
      }

      if (0 > (cmd = readCtrlLine())) {
        ERROR("Reading from %s failed.", TBCTRL_FIFOPATH);
      } else if (cmd != NULL) {

        // Value holders for sscanf.
        double valueIEEE754;
        unsigned int valueUInt;

        if        ( strEqualto("s", cmd) ||
                    strEqualto("step", cmd)) {

          m_doStep = 1;

        } else if ( (strStartswith("s ", cmd) ||
                     strStartswith("step ", cmd)) &&
                    (1 == sscanf(cmd, "%*s %d", &valueUInt))) {

          m_doStep = (valueUInt > 1) ? valueUInt : 1;

        } else if ( strEqualto("c", cmd) ||
                    strEqualto("continue", cmd) ) {

          m_doStep = -1;

        } else if ( strEqualto("d", cmd) ||
                    strEqualto("discontinue", cmd) ) {

          m_doStep = 0;

        } else if ( strEqualto("dumpon", cmd) ) {

          m_doDump = true;

        } else if ( strEqualto("dumpoff", cmd) ) {

          m_doDump = false;

        } else if ( (strStartswith("f ", cmd) ||
                     strStartswith("f_Hz ", cmd) ||
                     strStartswith("frequency_Hz ", cmd)) &&
                    (1 == sscanf(cmd, "%*s %lf", &valueIEEE754)) ) {

          setPeriodNsec((uint64_t)(1E9 / valueIEEE754));

        } else if ( (strStartswith("f_kHz ", cmd) ||
                     strStartswith("frequency_kHz ", cmd)) &&
                    (1 == sscanf(cmd, "%*s %lf", &valueIEEE754)) ) {

          setPeriodNsec((uint64_t)(1E6 / valueIEEE754));

        } else if ( (strStartswith("f_MHz ", cmd) ||
                     strStartswith("frequency_MHz ", cmd)) &&
                    (1 == sscanf(cmd, "%*s %lf", &valueIEEE754)) ) {

          setPeriodNsec((uint64_t)(1E3 / valueIEEE754));

        } else if ( (strStartswith("p ", cmd) ||
                     strStartswith("p_ns ", cmd) ||
                     strStartswith("period_ns ", cmd)) &&
                    (1 == sscanf(cmd, "%*s %d", &valueUInt))) {

          setPeriodNsec((uint64_t)(1E0 * valueUInt));

        } else if ( (strStartswith("p_us ", cmd) ||
                     strStartswith("period_us ", cmd)) &&
                    (1 == sscanf(cmd, "%*s %d", &valueUInt))) {

          setPeriodNsec((uint64_t)(1E3 * valueUInt));

        } else if ( (strStartswith("p_ms ", cmd) ||
                     strStartswith("period_ms ", cmd)) &&
                    (1 == sscanf(cmd, "%*s %d", &valueUInt))) {

          setPeriodNsec((uint64_t)(1E6 * valueUInt));

        } else if ( (strStartswith("p_s ", cmd) ||
                     strStartswith("period_s ", cmd)) &&
                    (1 == sscanf(cmd, "%*s %d", &valueUInt))) {

          setPeriodNsec((uint64_t)(1E9 * valueUInt));

        } else if ( strEqualto("r", cmd) ||
                    strEqualto("reset", cmd) ) {

          reset();

        } else if ( strEqualto("q", cmd) ||
                    strEqualto("quit", cmd) ) {

          break;

        } else if ( strEqualto("h", cmd) ||
                    strEqualto("help", cmd) ) {

 VERB("+-HELP----------------------------------------------------------------");
 VERB("| Each line is a command to the testbench.");
 VERB("| Runloop periodically (using walltime) tries to read command from");
 VERB("| %s then, evaluates one clock tick.", TBCTRL_FIFOPATH);
 VERB("| Available commands:");
 VERB("|    help/h");
 VERB("|        Display this message.");
 VERB("|    quit/q");
 VERB("|        Break out of runloop to quit the testbench.");
 VERB("|    frequency_Hz/f_Hz/f  <positive real>");
 VERB("|    frequency_kHz/f_kHz  <positive real>");
 VERB("|    frequency_MHz/f_MHz  <positive real>");
 VERB("|    period_ns/p_ns/p     <non-negative integer>");
 VERB("|    period_us/p_us       <non-negative integer>");
 VERB("|    period_ms/p_ms       <non-negative integer>");
 VERB("|    period_s/p_s         <non-negative integer>");
 VERB("|        Set runloop period.");
 VERB("|    step/s [positive integer]");
 VERB("|        Evaluate a N clock ticks, where N defaults to 1.");
 VERB("|    continue/c");
 VERB("|        Evaluate clock ticks indefinitely.");
 VERB("|    discontinue/d");
 VERB("|        Stop evaluating clock ticks indefinitely.");
 VERB("|    reset/r");
 VERB("|        Perform reset sequence with i_clk,i_rst.");
 VERB("|    dumpoff");
 VERB("|        Disable VCD dumping.");
 VERB("|    dumpon");
 VERB("|        Re-enable VCD dumping.");
 VERB("+---------------------------------------------------------------------");

        } else {
          VERB("  Unknown command \"%s\"", cmd);
        }

      }

      if (0 != m_doStep) tick();

      if (0 < m_doStep) m_doStep--;

    }

    VERB("  Exit");
    return;
  }

}; // }}}

#endif // _VERILATORTB_H
