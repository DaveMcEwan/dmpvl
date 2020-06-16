
#include <stdio.h>
#include <stdlib.h>

#include "verilated.h"
#include "verilated_vcd_c.h"

#include "VerilatorTbCtrl.h"

#include "Vcorrelator_tb.h"
#include "Vcorrelator_tb__Dpi.h"

#ifndef N_CYCLES
const int N_CYCLES = 100;
#endif

// NOTE: This tb mostly exists to provide waveforms so all checking is
// performed in Verilog components.
int main(int argc, char **argv, char **env) {

  Verilated::commandArgs(argc, argv);
  VerilatorTbCtrl<Vcorrelator_tb> *tb =
    new VerilatorTbCtrl<Vcorrelator_tb>("build/correlator_tb.verilator.vcd");

  tb->run(N_CYCLES);

  delete tb;
  exit(EXIT_SUCCESS);
}

