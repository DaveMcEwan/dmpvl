
#include <stdio.h>

#include "Vfxcs_tb.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

int main(int argc, char **argv, char **env) {

  Verilated::commandArgs(argc, argv);

  int unsigned t = 0;
  int unsigned n_errors = 0;

  // Init top verilog instance and trace dump.
  Vfxcs_tb* fxcs_tb = new Vfxcs_tb;
  Verilated::traceEverOn(true);
  VerilatedVcdC* vcd = new VerilatedVcdC;
  fxcs_tb->trace (vcd, 99);
  vcd->open ("build/fxcs_tb.verilator.vcd");

  // Initialize simulation inputs
  fxcs_tb->fxcs_7_i_vector = 0;
  fxcs_tb->fxcs_9_i_vector = 0;
  fxcs_tb->fxcs_16_i_vector = 0;

  fxcs_tb->fxcs_7_i_target = 0;
  fxcs_tb->fxcs_9_i_target = 0;
  fxcs_tb->fxcs_16_i_target = 0;
  fxcs_tb->eval();
  vcd->dump(t++);

  if (fxcs_tb->fxcs_7_o_onehot != fxcs_tb->fxcs_7_abstract_o_onehot) {
    printf("ERROR: Initial fxcs_7.o_onehot, %x, %x\n",
      fxcs_tb->fxcs_7_o_onehot,
      fxcs_tb->fxcs_7_abstract_o_onehot);
    n_errors++;
  }

  if (fxcs_tb->fxcs_9_o_onehot != fxcs_tb->fxcs_9_abstract_o_onehot) {
    printf("ERROR: Initial fxcs_9.o_onehot, %x, %x\n",
      fxcs_tb->fxcs_9_o_onehot,
      fxcs_tb->fxcs_9_abstract_o_onehot);
    n_errors++;
  }

  if (fxcs_tb->fxcs_16_o_onehot != fxcs_tb->fxcs_16_abstract_o_onehot) {
    printf("ERROR: Initial fxcs_16.o_onehot, %x, %x\n",
      fxcs_tb->fxcs_16_o_onehot,
      fxcs_tb->fxcs_16_abstract_o_onehot);
    n_errors++;
  }

  for (int unsigned tgt = 0; tgt < 16; tgt++) {
    for (int unsigned vec = 0; vec < (1 << 16); vec++) {
      fxcs_tb->fxcs_7_i_target = tgt % 7;
      fxcs_tb->fxcs_9_i_target = tgt % 9;
      fxcs_tb->fxcs_16_i_target = tgt % 16;

      fxcs_tb->fxcs_7_i_vector = vec & 0x7f;
      fxcs_tb->fxcs_9_i_vector = vec & 0x1ff;
      fxcs_tb->fxcs_16_i_vector = vec & 0xffff;

      fxcs_tb->eval();
      vcd->dump(t++);

      if (fxcs_tb->fxcs_7_o_onehot != fxcs_tb->fxcs_7_abstract_o_onehot) {
        printf("ERROR: t=%d, vec=0x%x, tgt=%d, fxcs_7.o_onehot, %x, %x\n",
          t, vec, tgt,
          fxcs_tb->fxcs_7_o_onehot,
          fxcs_tb->fxcs_7_abstract_o_onehot);
        n_errors++;
      }

      if (fxcs_tb->fxcs_9_o_onehot != fxcs_tb->fxcs_9_abstract_o_onehot) {
        printf("ERROR: t=%d, vec=0x%x, tgt=%d, fxcs_9.o_onehot, %x, %x\n",
          t, vec, tgt,
          fxcs_tb->fxcs_9_o_onehot,
          fxcs_tb->fxcs_9_abstract_o_onehot);
        n_errors++;
      }

      if (fxcs_tb->fxcs_16_o_onehot != fxcs_tb->fxcs_16_abstract_o_onehot) {
        printf("ERROR: t=%d, vec=0x%x, tgt=%d, fxcs_16.o_onehot, %x, %x\n",
          t, vec, tgt,
          fxcs_tb->fxcs_16_o_onehot,
          fxcs_tb->fxcs_16_abstract_o_onehot);
        n_errors++;
      }
    }

    if (n_errors) {
      break;
    }
  }

  // Last couple of evaluations just for pretty waves.
  fxcs_tb->fxcs_7_i_vector = 0;
  fxcs_tb->fxcs_9_i_vector = 0;
  fxcs_tb->fxcs_16_i_vector = 0;
  fxcs_tb->eval();
  vcd->dump(t++);
  vcd->dump(t++);

  vcd->close();
  exit(n_errors);
}

