
#include <stdio.h>
#include <stdlib.h>

#include "verilated.h"
#include "verilated_vcd_c.h"
#include "VerilatorTb.h"
#include "VSignalPortAssignment.h"

int main(int argc, char **argv, char **env) {

  Verilated::commandArgs(argc, argv);
  VerilatorTb<VSignalPortAssignment> *tb = new VerilatorTb<VSignalPortAssignment>();

  tb->opentrace("verilator.vcd");
  tb->m_trace->dump(0); // Initialize waveform at beginning of time.
  // Initialize simulation inputs
  tb->reset();

  while (tb->tickcount() < 1) {
    tb->tick(); // Checks performed at negedge times.
  }

  tb->closetrace();
  exit(EXIT_SUCCESS);
}

