
#include <stdio.h>
#include <stdlib.h>

#include "Vtestbench.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

template <class VA> class TESTB { // {{{
public:
  VA                *m_core;
  VerilatedVcdC     *m_trace;
  uint64_t          m_tickcount;

  TESTB(void) : m_trace(NULL), m_tickcount(0l) {
    m_core = new VA;
    Verilated::traceEverOn(true);
    m_core->i_clk = 0;
    m_core->i_rstn = 0;
    eval(); // Get our initial values set properly.
  }

  virtual ~TESTB(void) {
    closetrace();
    delete m_core;
    m_core = NULL;
  }

  virtual void opentrace(const char *vcdname) {
    if (!m_trace) {
        m_trace = new VerilatedVcdC;
        m_core->trace(m_trace, 99);
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
    m_core->eval();
  }

  virtual void tick(void) {
      m_tickcount++;

      // Make sure we have our evaluations straight before the top
      // of the clock.
      // This is necessary since some of the connection modules may have made
      // changes, for which some logic depends.
      // This forces that logic to be recalculated before the top of the clock.
      eval();
      //if (m_core->o_dumpon && m_trace)
      //    m_trace->dump((uint64_t)(10*m_tickcount-2));

      m_core->i_clk = 1;
      eval();
      if (m_core->o_dumpon && m_trace)
          m_trace->dump((uint64_t)(10*m_tickcount));

      m_core->i_clk = 0;
      eval();
      //if (m_core->o_dumpon && m_trace)
      //    m_trace->dump((uint64_t)(10*m_tickcount+5));

      if (m_trace)
          m_trace->flush();
  }

  virtual void reset(void) {
    m_core->i_rstn = 0;
    for (int i = 0; i < 5; i++)
        tick();
    m_core->i_rstn = 1;
  }

  unsigned long tickcount(void) {
    return m_tickcount;
  }

  virtual bool done(void) {
    return Verilated::gotFinish();
  }
}; // }}}

int main(int argc, char **argv, char **env) {

    Verilated::commandArgs(argc, argv);
    TESTB<Vtestbench> *tb = new TESTB<Vtestbench>();
    tb->opentrace("build/testbench.verilator.vcd");

    // Initialize waveform at beginning of time.
    if (tb->m_core->o_dumpon && tb->m_trace)
        tb->m_trace->dump(0);

    tb->reset();
    while (!tb->done()) {
        tb->tick();
    }

    tb->closetrace();
    exit(EXIT_SUCCESS);
}
