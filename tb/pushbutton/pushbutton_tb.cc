
#include <stdlib.h>

#include "verilated.h"
#include "verilated_vcd_c.h"
#include "VerilatorTb.h"
#include "Vpushbutton_tb.h"

#ifndef N_CYCLES
const int N_CYCLES = 100;
#endif

int main(int argc, char **argv, char **env) {

  Verilated::commandArgs(argc, argv);
  VerilatorTb<Vpushbutton_tb> *tb = new VerilatorTb<Vpushbutton_tb>();
  tb->opentrace("build/pushbutton_tb.verilator.vcd");
  tb->m_trace->dump(0); // Initialize waveform at beginning of time.

  // Initialize simulation inputs
  tb->m_dut->i_cg = 0;
  tb->m_dut->common_i_button = 0;
  tb->reset();

  // Run simulation for N_CYCLES clock periods.
  while (tb->tickcount() < N_CYCLES) {

    tb->tick(); // Checks performed at negedge times (tickcount*10+5).

    // TODO? Verilator checks here

    // Drivers evaluated at tickcount*10-2
    tb->m_dut->i_cg = (rand() % 10) != 0; // Drop i_cg 1/10.
  }

  tb->closetrace();
  exit(EXIT_SUCCESS);
}

