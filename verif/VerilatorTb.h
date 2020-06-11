#ifndef _VERILATORTB_H

#include <stdbool.h>
#include <stdio.h>

typedef enum {ERROR, WARN, NOTE} TbPrintLevel;

template <class VA> class VerilatorTb { // {{{
public:
  VA*               m_dut;
  VerilatedVcdC*    m_trace;
  uint64_t          m_tickcount;
  bool              m_dodump;

  VerilatorTb(void) : m_trace(NULL), m_tickcount(0l) {
    m_dut = new VA;
    Verilated::traceEverOn(true);
    m_dut->i_clk = 0;
    m_dut->i_rst = 1;
    m_dodump = true;
    eval(); // Get our initial values set properly.
  }

  virtual ~VerilatorTb(void) {
    closetrace();
    delete m_dut;
    m_dut = NULL;
  }

  virtual void opentrace(const char *vcdname) {
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
    if (m_dodump && m_trace) {
      m_trace->dump((uint64_t)(10*m_tickcount));
    }

    m_dut->i_clk = 0;
    eval();
    if (m_dodump && m_trace) {
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
}; // }}}

#endif // _VERILATORTB_H
