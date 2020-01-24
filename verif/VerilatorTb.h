
template <class VA> class VerilatorTb { // {{{
public:
  VA*               m_core;
  VerilatedVcdC*    m_trace;
  uint64_t          m_tickcount;

  VerilatorTb(void) : m_trace(NULL), m_tickcount(0l) {
    m_core = new VA;
    Verilated::traceEverOn(true);
    m_core->i_clk = 0;
    m_core->i_rst = 1;
    eval(); // Get our initial values set properly.
  }

  virtual ~VerilatorTb(void) {
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
    if (m_trace) m_trace->dump((uint64_t)(10*m_tickcount-2));

    m_core->i_clk = 1;
    eval();
    if (m_trace) m_trace->dump((uint64_t)(10*m_tickcount));

    m_core->i_clk = 0;
    eval();
    if (m_trace) {
      m_trace->dump((uint64_t)(10*m_tickcount+5));
      m_trace->flush();
    }
  }

  virtual void reset(void) {
    m_core->i_rst = 1;
    for (int i = 0; i < 5; i++)
      tick();
    m_core->i_rst = 0;
  }

  unsigned long tickcount(void) {
    return m_tickcount;
  }

  virtual bool done(void) {
    return Verilated::gotFinish();
  }
}; // }}}

