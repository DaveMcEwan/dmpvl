
#include <stdio.h>

#include "VmssbIdx_tb.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

int main(int argc, char **argv, char **env) {

  Verilated::commandArgs(argc, argv);

  int unsigned n_errors = 0;

  // Init top verilog instance and trace dump.
  VmssbIdx_tb* mssbIdx_tb = new VmssbIdx_tb;
  Verilated::traceEverOn(true);
  VerilatedVcdC* vcd = new VerilatedVcdC;
  mssbIdx_tb->trace (vcd, 99);
  vcd->open ("build/mssbIdx_tb.verilator.vcd");

  // Initialize simulation inputs
  mssbIdx_tb->mssbIdx_7_i_vector = 0;
  mssbIdx_tb->mssbIdx_9_i_vector = 0;
  mssbIdx_tb->mssbIdx_16_i_vector = 0;
  mssbIdx_tb->eval();
  vcd->dump(0);

  if (mssbIdx_tb->mssbIdx_7_o_index != 0) {
    printf("ERROR: Initial mssbIdx_7 != 0\n");
    n_errors++;
  }
  if (mssbIdx_tb->mssbIdx_9_o_index != 0) {
    printf("ERROR: Initial mssbIdx_9 != 0\n");
    n_errors++;
  }
  if (mssbIdx_tb->mssbIdx_16_o_index != 0) {
    printf("ERROR: Initial mssbIdx_16 != 0\n");
    n_errors++;
  }

  if (mssbIdx_tb->mssbIdx_7_o_valid != 0) {
    printf("ERROR: Initial mssbIdx_7 != invalid\n");
    n_errors++;
  }
  if (mssbIdx_tb->mssbIdx_9_o_valid != 0) {
    printf("ERROR: Initial mssbIdx_9 != invalid\n");
    n_errors++;
  }
  if (mssbIdx_tb->mssbIdx_16_o_valid != 0) {
    printf("ERROR: Initial mssbIdx_16 != invalid\n");
    n_errors++;
  }

  for (int unsigned t = 0; t < (1 << 16); t++) {
    mssbIdx_tb->mssbIdx_7_i_vector = t & 0x7f;
    mssbIdx_tb->mssbIdx_9_i_vector = t & 0x1ff;
    mssbIdx_tb->mssbIdx_16_i_vector = t & 0xffff;

    mssbIdx_tb->eval();
    vcd->dump(t+1);

    if (t < 7) {
      if (mssbIdx_tb->mssbIdx_7_o_index != t) {
        printf("ERROR: t=%d mssbIdx_7 != %d\n", t, t);
        n_errors++;
      }

      if (mssbIdx_tb->mssbIdx_7_o_valid == 0) {
        printf("ERROR: t=%d mssbIdx_7 == invalid\n", t);
        n_errors++;
      }
    }

    if (t < 9) {
      if (mssbIdx_tb->mssbIdx_9_o_index != t) {
        printf("ERROR: t=%d mssbIdx_9 != %d\n", t, t);
        n_errors++;
      }

      if (mssbIdx_tb->mssbIdx_9_o_valid == 0) {
        printf("ERROR: t=%d mssbIdx_9 == invalid\n", t);
        n_errors++;
      }
    }

    if (mssbIdx_tb->mssbIdx_16_o_index != t) {
      printf("ERROR: t=%d mssbIdx_16 != %d\n", t, t);
      n_errors++;
    }
    if (mssbIdx_tb->mssbIdx_16_o_valid == 0) {
      printf("ERROR: t=%d mssbIdx_16 == invalid\n", t);
      n_errors++;
    }
  }

  // Last couple of evaluations just for pretty waves.
  mssbIdx_tb->mssbIdx_7_i_vector = 0;
  mssbIdx_tb->mssbIdx_9_i_vector = 0;
  mssbIdx_tb->mssbIdx_16_i_vector = 0;
  mssbIdx_tb->eval();
  vcd->dump(17);
  vcd->dump(18);

  vcd->close();
  exit(n_errors);
}

