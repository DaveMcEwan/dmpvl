#ifndef _VERILATORTBCTRL_H
#define _VERILATORTBCTRL_H

#include <fcntl.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>

#include "dmpvlCommon.h"

#define TBCTRL_BUFLEN 32

typedef enum {Error, Warn, Note} TbCtrl_PrintLevel;

typedef enum {
  None,
  Step1,            // s[tep]
  StepN,            // s[tep] [<0123>]
  Continue,         // c[ontinue]
  Discontinue,      // d[iscontinue]
  DumpOn,           // dumpon
  DumpOff,          // dumpoff
  Timebase,         // t[imebase] (Z | absolute | relative)
  Frequency,        // f[requency] <0123>
  Reset,            // r[eset]
  Quit              // q[uit]
} TbCtrl_CommandType;



template <class VA> class VerilatorTbCtrl { // {{{
public:
  VA*               m_dut;
  VerilatedVcdC*    m_trace;
  uint64_t          m_tickcount;
  int               m_ctrlfifo;
  bool              m_doDump;
  int               m_doStep;
  double            m_tickFreq_Hz;

  VerilatorTbCtrl(const char* vcdname) : m_trace(NULL), m_tickcount(0l) {
    m_dut = new VA;
    Verilated::traceEverOn(true);
    m_dut->i_clk = 0;
    m_dut->i_rst = 1;
    m_doDump = true;
    eval(); // Get our initial values set properly.
    opentrace(vcdname);
    openctrl("tbCtrl");
  }

  virtual ~VerilatorTbCtrl(void) {
    closetrace();
    close(m_ctrlfifo);
    delete m_dut;
    m_dut = NULL;
  }

  virtual void openctrl(const char* fifoname) {
    if (0 > mkfifo(fifoname, 0666)) {
      ERROR("Cannot open control fifo.");
    }

    m_ctrlfifo = open(fifoname, O_RDONLY | O_NONBLOCK);
  }

  virtual void opentrace(const char* vcdname) {
    if (!m_trace) {
      m_trace = new VerilatedVcdC;
      m_dut->trace(m_trace, 99);
      m_trace->open(vcdname);
    }
  }

  virtual void closetrace(void) {
    if (m_trace) {
      m_trace->close();
      delete m_trace;
      m_trace = NULL;
    }
  }

  virtual void eval(void) {
    m_dut->eval();
  }

  // Call from loop {check, drive, tick}
  virtual void tick(void) {
    // check
    // drive
    // rise eval dump
    // fall eval dump

    m_dut->i_clk = 1;
    eval();
    if (m_doDump && m_trace) {
      m_trace->dump((uint64_t)(10*m_tickcount));
    }

    m_dut->i_clk = 0;
    eval();
    if (m_doDump && m_trace) {
      m_trace->dump((uint64_t)(10*m_tickcount+5));
      m_trace->flush();
    }

    m_tickcount++;
  }

  virtual void reset(void) {
    m_dut->i_rst = 1;
    for (int i = 0; i < 5; i++)
      tick();
    m_dut->i_rst = 0;
  }

  unsigned long tickcount(void) {
    return m_tickcount;
  }

  virtual bool done(void) {
    return Verilated::gotFinish();
  }

  virtual char* readCtrlLine(const int fd) {
    static int i = 0;
    static char buf[TBCTRL_BUFLEN] = {0};

    char* ret_line      = buf;
    char* ret_error     = (char*)(-1);
    char* ret_notReady  = (char*)(NULL);

    int nRead;
    char* ret;

    while (1) {
      // https://linux.die.net/man/2/read
      if (0 > (nRead = read(fd, &buf[i], 1))) {
        // Cannot get char either because there's no data in fifo, or an error.
        bool blocking = (EAGAIN == errno) || (EWOULDBLOCK == errno);
        ret = blocking ? ret_notReady : ret_error;
        break;
      }

      // Zero characters read, without causing an error.
      assert(1 != nRead);

      if (buf[i] == '\n') {
        // End of line --> return pointer to buf.
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

  virtual TbCtrl_CommandType getCommandType() {
    char* cmd;
    TbCtrl_CommandType ret = None;

    if (0 > (cmd = readCtrlLine(m_ctrlfifo))) {
      ERROR("Reading from tbCtrl failed.");
    } else if (cmd != NULL) {

      if      ( strEqualto("s", cmd) ||
                strEqualto("step", cmd))            ret = Step1;

      else if ( strStartswith("s ", cmd) ||
                strStartswith("step ", cmd) )       ret = StepN;

      else if ( strEqualto("c", cmd) ||
                strEqualto("continue", cmd) )       ret = Continue;

      else if ( strEqualto("d", cmd) ||
                strEqualto("discontinue", cmd) )    ret = Discontinue;

      else if ( strEqualto("dumpon", cmd) )         ret = DumpOn;

      else if ( strEqualto("dumpoff", cmd) )        ret = DumpOff;

      /*
      else if ( strStartswith("t ", cmd) ||
                strStartswith("timebase ", cmd) )   ret = Timebase;
      */

      else if ( strStartswith("f ", cmd) ||
                strStartswith("frequency ", cmd) )  ret = Frequency;

      else if ( strEqualto("r", cmd) ||
                strEqualto("reset", cmd) )          ret = Reset;

      else if ( strEqualto("q", cmd) ||
                strEqualto("quit", cmd) )           ret = Quit;

    }

    return ret;
  }

  virtual bool run(int maxNCycles) {
    m_doStep = 0;

    while (tickcount() < maxNCycles) {
      // TODO: Sleep for some amount of time.

      TbCtrl_CommandType cmd = getCommandType();

      if (Step1 == cmd) {
        m_doStep = 1;
      } else if (StepN == cmd) {
        m_doStep = 1; // TODO: N steps
      } else if (Continue == cmd) {
        m_doStep = -1;
      } else if (Discontinue == cmd) {
        m_doStep = 0;
      } else if (DumpOn == cmd) {
        m_doDump = true;
      } else if (DumpOff == cmd) {
        m_doDump = false;
      /*
      } else if (Timebase == cmd) {
        // TODO: Get value in {Z, absolute, relative}
      */
      } else if (Frequency == cmd) {
        // TODO: Get value as float
      } else if (Reset == cmd) {
        reset();
      } else if (Quit == cmd) {
        break;
      }

      if (0 != m_doStep) tick();

      if (0 < m_doStep) m_doStep--;
    }
  }
}; // }}}

#if 0
// Create a fifo and open the read side.
int tbCtrl_enter(char* path) {
  if (0 != atexit(tbCtrl_exit)) {
    ERROR("Cannot register exit function.");
  }
  return (0 > mkfifo(path, 0666)) ? -1 : open(path, O_RDONLY | O_NONBLOCK);
}

// Close read side and remove fifo.
void tbCtrl_exit(int fd) {
  // NOTE: Called within exit().
  // https://linux.die.net/man/2/close
  if (0 != close(fd)) {
    fprintf(stderr, "ERROR: %s", strerror(errno));
  }
}
#endif

#endif // _VERILATORTB_H
