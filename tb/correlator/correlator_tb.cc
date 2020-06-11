
#include <stdio.h>
#include <stdlib.h>

#include "verilated.h"
#include "verilated_vcd_c.h"

#include "VerilatorTb.h"

#include "Vcorrelator_tb.h"
#include "Vcorrelator_tb__Dpi.h"

#ifndef N_CYCLES
const int N_CYCLES = 100;
#endif

#define TBCTRL_BUFLEN 32

bool strStartswith(const char* prefix, const char* str) {
  return (0 == strncmp(prefix, str, strlen(prefix)));
}

bool strEqualto(const char* cmp, const char* str) {
  return (0 == strncmp(cmp, str, TBCTRL_BUFLEN));
}

/*
Assume fd is opened with O_NONBLOCK.
Read one char at a time until
  1. found a newline -->
    print info line?
    reset index
    return pointer to buf
  2. fifo starts blocking -->
    return NULL (not ready yet)
  3. buf is full -->
    print warn line?
    reset index
    return -1 (error occurred)
*/
char* tbCtrl_readLine(const int fd) {
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

typedef enum {
  None,
  Step,             // s[tep] [<0123>]
  Continue,         // c[ontinue]
  Discontinue,      // d[iscontinue]
  DumpOn,           // dumpon
  DumpOff,          // dumpoff
  Timebase,         // t[imebase] (Z | absolute | relative)
  Frequency,        // f[requency] <0123>
  Reset,            // r[eset]
  Quit              // q[uit]
} tbCtrl_CommandType;

// Attempt to read a command from fifo
tbCtrl_CommandType tbCtrl_getCommandType(const int fd) {
  char* cmd;
  tbCtrl_CommandType ret = None;

  if (0 > (cmd = tbCtrl_readLine(fd))) {

    // TODO: error message?
    exit(EXIT_FAILURE);

  } else if (cmd != NULL) {

    if      ( strEqualto("s", cmd) ||
              strEqualto("step", cmd) ||
              strStartswith("s ", cmd) ||
              strStartswith("step ", cmd) )       ret = Step;

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

// NOTE: This tb mostly exists to provide waveforms so all checking is
// performed in Verilog components.
int main(int argc, char **argv, char **env) {

  Verilated::commandArgs(argc, argv);
  VerilatorTb<Vcorrelator_tb> *tb = new VerilatorTb<Vcorrelator_tb>();
  tb->opentrace("build/correlator_tb.verilator.vcd");
  tb->m_trace->dump(0); // Initialize waveform at beginning of time.

  // Initialize simulation inputs
  tb->reset();

  // TODO: mkfifo tbCtrl

  while (tb->tickcount() < N_CYCLES) {
    // TODO: Sleep for some amount of time.

    tbCtrl_CommandType cmd = tbCtrl_getCommandType(tbCtrl_fd);
    if (Step == cmd) {
      doStep = 1; // TODO: N steps
    } else if (Continue == cmd) {
      doStep = -1;
    } else if (Discontinue == cmd) {
      doStep = 0;
    } else if (DumpOn == cmd) {
      tb->m_dodump = true;
    } else if (DumpOff == cmd) {
      tb->m_dodump = false;
    /*
    } else if (Timebase == cmd) {
      // TODO: Get value in {Z, absolute, relative}
    */
    } else if (Frequency == cmd) {
      // TODO: Get value as float
    } else if (Reset == cmd) {
      tb->reset();
    } else if (Quit == cmd) {
      break;
    }

    if (0 != doStep) tb->tick();

    if (0 < doStep) doStep--;
  }

  tb->closetrace();
  exit(EXIT_SUCCESS);
}

