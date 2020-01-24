
#include <stdio.h>

#include "VonehotIdx_tb.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

int main(int argc, char **argv, char **env) {

  Verilated::commandArgs(argc, argv);

  int unsigned vec;
  int unsigned n_errors = 0;

  // Init top verilog instance and trace dump.
  VonehotIdx_tb* onehotIdx_tb = new VonehotIdx_tb;
  Verilated::traceEverOn(true);
  VerilatedVcdC* vcd = new VerilatedVcdC;
  onehotIdx_tb->trace (vcd, 99);
  vcd->open ("build/onehotIdx_tb.verilator.vcd");

  // Initialize simulation inputs
  onehotIdx_tb->onehotIdx_9_i_onehot = 0;
  onehotIdx_tb->onehotIdx_16_i_onehot = 0;
  onehotIdx_tb->eval();
  vcd->dump(0);
  if (onehotIdx_tb->onehotIdx_9_o_index != 0) {
    printf("ERROR: Initial onehotIdx_9 != 0\n");
    n_errors++;
  }
  if (onehotIdx_tb->onehotIdx_16_o_index != 0) {
    printf("ERROR: Initial onehotIdx_16 != 0\n");
    n_errors++;
  }
  if (onehotIdx_tb->onehotIdx_9_o_valid != 0) {
    printf("ERROR: Initial onehotIdx_9 != invalid\n");
    n_errors++;
  }
  if (onehotIdx_tb->onehotIdx_16_o_valid != 0) {
    printf("ERROR: Initial onehotIdx_16 != invalid\n");
    n_errors++;
  }

  for (int unsigned t = 0; t < 16; t++) {
    vec = 1 << t;
    onehotIdx_tb->onehotIdx_9_i_onehot = vec & 0x1ff;
    onehotIdx_tb->onehotIdx_16_i_onehot = vec & 0xffff;

    onehotIdx_tb->eval();
    vcd->dump(t+1);

    if (t < 9) {
      if (onehotIdx_tb->onehotIdx_9_o_index != t) {
        printf("ERROR: t=%d onehotIdx_9 != %d\n", t, t);
        n_errors++;
      }

      if (onehotIdx_tb->onehotIdx_9_o_valid == 0) {
        printf("ERROR: t=%d onehotIdx_9 == invalid\n", t);
        n_errors++;
      }
    }

    if (onehotIdx_tb->onehotIdx_16_o_index != t) {
      printf("ERROR: t=%d onehotIdx_16 != %d\n", t, t);
      n_errors++;
    }
    if (onehotIdx_tb->onehotIdx_16_o_valid == 0) {
      printf("ERROR: t=%d onehotIdx_16 == invalid\n", t);
      n_errors++;
    }
  }

  // Last couple of evaluations just for pretty waves.
  onehotIdx_tb->onehotIdx_9_i_onehot = 0;
  onehotIdx_tb->onehotIdx_16_i_onehot = 0;
  onehotIdx_tb->eval();
  vcd->dump(17);
  vcd->dump(18);

  vcd->close();
  exit(n_errors);
}

