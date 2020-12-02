
#include <stdio.h>
#include <stdlib.h>

#include "verilated.h"
#include "verilated_vcd_c.h"
#include "VerilatorTb.h"
#include "VfifoScoreboard_tb.h"

#ifndef N_CYCLES
const int N_CYCLES = 100;
#endif

int main(int argc, char **argv, char **env) {

  Verilated::commandArgs(argc, argv);
  VerilatorTb<VfifoScoreboards_tb> *tb = new VerilatorTb<VfifoScoreboard_tb>();
  tb->opentrace("build/fifoScoreboard_tb.verilator.vcd");
  tb->m_trace->dump(0); // Initialize waveform at beginning of time.

  // Initialize simulation inputs
  tb->reset();

  // Run simulation for N_CYCLES clock periods.
  while (tb->tickcount() < N_CYCLES) {
    tb->tick(); // Checks performed at negedge times.
  }

  tb->closetrace();
  exit(EXIT_SUCCESS);
}

