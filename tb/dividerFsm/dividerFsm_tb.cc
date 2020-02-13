
#include <stdlib.h>

#include "verilated.h"
#include "verilated_vcd_c.h"
#include "VerilatorTb.h"
#include "VdividerFsm_tb.h"

#ifndef N_CYCLES
const int N_CYCLES = 100;
#endif

void tbPrint(
    TbPrintLevel level,
    unsigned int t, // time
    char const * msg, ...
) {
    const char * levels[] = {"ERROR", "WARNING", "NOTE"};

    printf("%s:t%d:%s: ", levels[level], t);

    va_list vargs;
    va_start(vargs, msg);
    vprintf(msg, vargs);
    va_end(vargs);

    printf("\n");
    return;
}

int main(int argc, char **argv, char **env) {

  Verilated::commandArgs(argc, argv);
  VerilatorTb<VdividerFsm_tb> *tb = new VerilatorTb<VdividerFsm_tb>();
  tb->opentrace("build/dividerFsm_tb.verilator.vcd");
  tb->m_trace->dump(0); // Initialize waveform at beginning of time.

  // Initialize simulation inputs
  tb->m_core->i_cg = 0;
  tb->m_core->common_i_begin = 0;
  tb->m_core->common_i_dividend = 0x55;
  tb->m_core->common_i_divisor = 0x55;
  tb->reset();
  tbPrint(NOTE, tb->tickcount(), "Finished reset()");

  // Run simulation for N_CYCLES clock periods.
  while (tb->tickcount() < N_CYCLES) {

    tb->tick(); // Checks performed at negedge times (tickcount*10+5).

    // TODO? Verilator checks here
    // NOTE: Verilog part of testbench has assertions for checking.

    // Drivers evaluated at tickcount*10-2
    tb->m_core->i_cg = (rand() % 4) != 0; // Drop i_cg 1/4.
    if (tb->m_core->dividerFsm_8_o_busy) {
      tb->m_core->common_i_begin = 0;
    } else {
      tb->m_core->common_i_begin = (rand() % 8) == 0;
      tb->m_core->common_i_dividend = rand() & 0xff;
      tb->m_core->common_i_divisor = rand() & 0xff;
    }
  }

  tb->closetrace();
  exit(EXIT_SUCCESS);
}

