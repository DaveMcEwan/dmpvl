
#include <stdio.h>
#include <stdlib.h>

#include "verilated.h"
#include "verilated_vcd_c.h"
#include "VerilatorTb.h"
#include "Vpraxi.h"

int main(int argc, char **argv, char **env) {

  Verilated::commandArgs(argc, argv);
  VerilatorTb<Vpraxi> *tb = new VerilatorTb<Vpraxi>();
  tb->opentrace("build/praxi.verilator.vcd");
  tb->m_trace->dump(0); // Initialize waveform at beginning of time.

  tb->reset();
  while (!tb->done()) {
    tb->tick();
  }

  tb->closetrace();

  exit(EXIT_SUCCESS);
}
