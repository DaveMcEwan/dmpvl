
#include <stdio.h>

#include "VlogdropWindow_tb.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

// logdropWindow_tb.sv - Exhaustively test all input combinations for logdropWindow.
int main(int argc, char **argv, char **env) {

  Verilated::commandArgs(argc, argv);

  int unsigned t = 0;
  int unsigned n_errors = 0;

  // Init top verilog instance and trace dump.
  VlogdropWindow_tb* logdropWindow_tb = new VlogdropWindow_tb;
  Verilated::traceEverOn(true);
  VerilatedVcdC* vcd = new VerilatedVcdC;
  logdropWindow_tb->trace (vcd, 99);
  vcd->open ("build/logdropWindow_tb.verilator.vcd");

  // Initialize simulation inputs
  logdropWindow_tb->logdropWindow_i_t = 0;
  logdropWindow_tb->logdropWindow_i_x = 0;
  logdropWindow_tb->eval();
  vcd->dump(t++);

  if (logdropWindow_tb->logdropWindow_A_o_y != logdropWindow_tb->logdropWindow_A_abstract_o_y) {
    printf("ERROR: Initial logdropWindow_A_u.o_y, %x, %x\n",
      logdropWindow_tb->logdropWindow_A_o_y,
      logdropWindow_tb->logdropWindow_A_abstract_o_y);
    n_errors++;
  }

  if (logdropWindow_tb->logdropWindow_B_o_y != logdropWindow_tb->logdropWindow_B_abstract_o_y) {
    printf("ERROR: Initial logdropWindow_B_u.o_y, %x, %x\n",
      logdropWindow_tb->logdropWindow_B_o_y,
      logdropWindow_tb->logdropWindow_B_abstract_o_y);
    n_errors++;
  }

  for (int unsigned i_x = 0; i_x < 2000; i_x++) {
    for (int unsigned i_t = 0; i_t < 200; i_t++) {
      logdropWindow_tb->logdropWindow_i_t = i_t;
      logdropWindow_tb->logdropWindow_i_x = i_x;
      logdropWindow_tb->eval();
      vcd->dump(t++);

      if (logdropWindow_tb->logdropWindow_A_o_y != logdropWindow_tb->logdropWindow_A_abstract_o_y) {
        printf("ERROR: t=%d, i_t=%d, i_x=%d, logdropWindow_A_u.o_y, %x, %x\n",
          t, i_t, i_x,
          logdropWindow_tb->logdropWindow_A_o_y,
          logdropWindow_tb->logdropWindow_A_abstract_o_y);
        n_errors++;
      }

      if (logdropWindow_tb->logdropWindow_B_o_y != logdropWindow_tb->logdropWindow_B_abstract_o_y) {
        printf("ERROR: t=%d, i_t=%d, i_x=%d, logdropWindow_B_u.o_y, %x, %x\n",
          t, i_t, i_x,
          logdropWindow_tb->logdropWindow_B_o_y,
          logdropWindow_tb->logdropWindow_B_abstract_o_y);
        n_errors++;
      }

      //if (n_errors) {
      //    break;
      //}
    }
  }

  // Last couple of evaluations just for pretty waves.
  logdropWindow_tb->logdropWindow_i_t = 0;
  logdropWindow_tb->logdropWindow_i_x = 0;
  logdropWindow_tb->eval();
  vcd->dump(t++);
  vcd->dump(t++);

  vcd->close();
  exit(n_errors);
}

