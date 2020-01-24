
#include <stdio.h>
#include <stdlib.h>

#include "verilated.h"
#include "verilated_vcd_c.h"
#include "VerilatorTb.h"
#include "Vprobsys0.h"

int main(int argc, char **argv, char **env) {

  Verilated::commandArgs(argc, argv);
  VerilatorTb<Vprobsys0> *tb = new VerilatorTb<Vprobsys0>();
  tb->opentrace("build/probsys0.verilator.vcd");
  tb->m_trace->dump(0); // Initialize waveform at beginning of time.

  tb->reset();
  while (!tb->done()) {
    tb->tick();
  }

  tb->closetrace();

  exit(EXIT_SUCCESS);
}
