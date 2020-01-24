
#include <stdio.h>

#include "Vpopcnt6_tb.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

// popcnt6_tb.sv - Exhaustively test all input combinations for popcnt6.
int main(int argc, char **argv, char **env) {

  Verilated::commandArgs(argc, argv);

  int unsigned t = 0;
  int unsigned n_errors = 0;

  // Init top verilog instance and trace dump.
  Vpopcnt6_tb* popcnt6_tb = new Vpopcnt6_tb;
  Verilated::traceEverOn(true);
  VerilatedVcdC* vcd = new VerilatedVcdC;
  popcnt6_tb->trace (vcd, 99);
  vcd->open ("build/popcnt6_tb.verilator.vcd");

  // Initialize simulation inputs
  popcnt6_tb->popcnt6_i_x = 0;
  popcnt6_tb->eval();
  vcd->dump(t++);

  if (popcnt6_tb->popcnt6_o_count != popcnt6_tb->popcnt6_abstract_o_count) {
    printf("ERROR: Initial popcnt6_u.o_count, %x, %x\n",
      popcnt6_tb->popcnt6_o_count,
      popcnt6_tb->popcnt6_abstract_o_count);
    n_errors++;
  }

  for (int unsigned i = 0; i < 200; i++) {
    popcnt6_tb->popcnt6_i_x = i & 0x3f;
    popcnt6_tb->eval();
    vcd->dump(t++);

    if (popcnt6_tb->popcnt6_o_count != popcnt6_tb->popcnt6_abstract_o_count) {
      printf("ERROR: t=%d, i=%d, popcnt6_u.o_count, %x, %x\n",
        t, i,
        popcnt6_tb->popcnt6_o_count,
        popcnt6_tb->popcnt6_abstract_o_count);
      n_errors++;
    }

    //if (n_errors) {
    //    break;
    //}
  }

  // Last couple of evaluations just for pretty waves.
  popcnt6_tb->popcnt6_i_x = 0;
  popcnt6_tb->eval();
  vcd->dump(t++);
  vcd->dump(t++);

  vcd->close();
  exit(n_errors);
}

