
#include <stdio.h>
#include <stdlib.h>

#include "Vw_rand.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

// w_rand.sv - Exhaustively test all input combinations for logdropWindow.
int main(int argc, char **argv, char **env) {

  Verilated::commandArgs(argc, argv);

  int unsigned t = 0;
  int unsigned n_errors = 0;

  // Init top verilog instance and trace dump.
  Vw_rand* w_rand = new Vw_rand;
  Verilated::traceEverOn(true);
  VerilatedVcdC* vcd = new VerilatedVcdC;
  w_rand->trace (vcd, 99);
  vcd->open ("build/w_rand.vcd");

  // Initialize simulation inputs
  w_rand->i_t = 0;
  w_rand->i_x = 0;
  w_rand->eval();
  vcd->dump(t++);

  srand(123);

  if (w_rand->A_o_y != w_rand->A_abstract_o_y) {
    printf("ERROR: Initial A_u.o_y, %x, %x\n",
      w_rand->A_o_y,
      w_rand->A_abstract_o_y);
    n_errors++;
  }

  FILE * fd_x;
  FILE * fd_y;
  fd_x = fopen("build/w_rand.i_x.bin", "wb");
  fd_y = fopen("build/w_rand.o_y.bin", "wb");

  for (int unsigned i_t = 0; i_t < 10000000; i_t++) {
    w_rand->i_t = i_t;
    w_rand->i_x = rand();
    w_rand->eval();
    vcd->dump(t++);

    fwrite(&(w_rand->A_i_x), 1, 1, fd_x);
    fwrite(&(w_rand->A_o_y), 1, 1, fd_y);

    if (w_rand->A_o_y != w_rand->A_abstract_o_y) {
      printf("ERROR: t=%d, i_t=%d, i_x=%d, A_u.o_y, %x, %x\n",
        t, i_t,
        w_rand->A_i_x,
        w_rand->A_o_y,
        w_rand->A_abstract_o_y);
      n_errors++;
    }

    //if (n_errors) {
    //    break;
    //}
  }

  fclose(fd_x);
  fclose(fd_y);

  // Last couple of evaluations just for pretty waves.
  w_rand->i_t = 0;
  w_rand->i_x = 0;
  w_rand->eval();
  vcd->dump(t++);
  vcd->dump(t++);

  vcd->close();
  exit(n_errors);
}

