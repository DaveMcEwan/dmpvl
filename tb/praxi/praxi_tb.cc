
#include <stdio.h>
#include <stdlib.h>

#include "verilated.h"
#include "verilated_vcd_c.h"
#include "VerilatorTb.h"
#include "Vpraxi_tb.h"

int main(int argc, char **argv, char **env) {

  Verilated::commandArgs(argc, argv);
  VerilatorTb<Vpraxi_tb> *tb = new VerilatorTb<Vpraxi_tb>();
  tb->opentrace("build/praxi_tb.verilator.vcd");
  tb->m_trace->dump(0); // Initialize waveform at beginning of time.

  tb->reset();
  while (tb->tickcount() < N_CYCLES) {
    tb->tick();
  }

  tb->closetrace();
  exit(EXIT_SUCCESS);
}
