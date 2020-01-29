
#include <stdio.h>
#include <stdlib.h>

#include "verilated.h"
#include "verilated_vcd_c.h"
#include "VerilatorTb.h"
#include "Vfifo_tb.h"
#include "fifo_model.h"

#ifndef N_CYCLES
const int N_CYCLES = 100;
#endif

int main(int argc, char **argv, char **env) {

  Verilated::commandArgs(argc, argv);
  VerilatorTb<Vfifo_tb> *tb = new VerilatorTb<Vfifo_tb>();
  tb->opentrace("build/fifo_tb.verilator.vcd");
  tb->m_trace->dump(0); // Initialize waveform at beginning of time.

  // Instance models to compare against the tb.
  FifoModel* model_8_8_mem = new FifoModel(8, 8, CIRCULAR, MEMORY);
  FifoModel* model_1_2_mem = new FifoModel(1, 2, CIRCULAR, MEMORY);
  FifoModel* model_5_5_mem = new FifoModel(5, 5, CIRCULAR, MEMORY);
  FifoModel* model_8_2_flops = new FifoModel(8, 2, CIRCULAR, FLOPS);

  // Initialize simulation inputs
  tb->m_core->common_cg = 0;
  tb->m_core->common_flush = 0;
  tb->m_core->common_push = 0;
  tb->m_core->common_pop = 0;
  tb->m_core->common_data = 0;
  tb->m_core->fifo_8_8_mem_i_data = 0x55;
  tb->m_core->fifo_1_2_mem_i_data = 0;
  tb->m_core->fifo_5_5_mem_i_data = 0x15;
  tb->m_core->fifo_8_2_flops_i_data = 0x55;
  tb->reset();

  // Run simulation for N_CYCLES clock periods.
  while (tb->tickcount() < N_CYCLES) {

    tb->tick(); // Checks performed at negedge times (tickcount*10+5).

    model_8_8_mem->check( // {{{
      tb->tickcount(),

      tb->m_core->i_clk,
      tb->m_core->i_clk,
      tb->m_core->common_cg,

      tb->m_core->common_flush,
      tb->m_core->common_push,
      tb->m_core->common_pop,

      tb->m_core->fifo_8_8_mem_i_data,
      tb->m_core->fifo_8_8_mem_o_data,

      tb->m_core->fifo_8_8_mem_o_empty,
      tb->m_core->fifo_8_8_mem_o_full,

      tb->m_core->fifo_8_8_mem_o_pushed,
      tb->m_core->fifo_8_8_mem_o_popped,

      tb->m_core->fifo_8_8_mem_o_wrptr,
      tb->m_core->fifo_8_8_mem_o_rdptr,

      tb->m_core->fifo_8_8_mem_o_valid,
      tb->m_core->fifo_8_8_mem_o_nEntries,

      tb->m_core->fifo_8_8_mem_o_entries
    ); // }}}

    model_1_2_mem->check( // {{{
      tb->tickcount(),

      tb->m_core->i_clk,
      tb->m_core->i_clk,
      tb->m_core->common_cg,

      tb->m_core->common_flush,
      tb->m_core->common_push,
      tb->m_core->common_pop,

      tb->m_core->fifo_1_2_mem_i_data,
      tb->m_core->fifo_1_2_mem_o_data,

      tb->m_core->fifo_1_2_mem_o_empty,
      tb->m_core->fifo_1_2_mem_o_full,

      tb->m_core->fifo_1_2_mem_o_pushed,
      tb->m_core->fifo_1_2_mem_o_popped,

      tb->m_core->fifo_1_2_mem_o_wrptr,
      tb->m_core->fifo_1_2_mem_o_rdptr,

      tb->m_core->fifo_1_2_mem_o_valid,
      tb->m_core->fifo_1_2_mem_o_nEntries,

      tb->m_core->fifo_1_2_mem_o_entries
    ); // }}}

    model_5_5_mem->check( // {{{
      tb->tickcount(),

      tb->m_core->i_clk,
      tb->m_core->i_clk,
      tb->m_core->common_cg,

      tb->m_core->common_flush,
      tb->m_core->common_push,
      tb->m_core->common_pop,

      tb->m_core->fifo_5_5_mem_i_data,
      tb->m_core->fifo_5_5_mem_o_data,

      tb->m_core->fifo_5_5_mem_o_empty,
      tb->m_core->fifo_5_5_mem_o_full,

      tb->m_core->fifo_5_5_mem_o_pushed,
      tb->m_core->fifo_5_5_mem_o_popped,

      tb->m_core->fifo_5_5_mem_o_wrptr,
      tb->m_core->fifo_5_5_mem_o_rdptr,

      tb->m_core->fifo_5_5_mem_o_valid,
      tb->m_core->fifo_5_5_mem_o_nEntries,

      tb->m_core->fifo_5_5_mem_o_entries
    ); // }}}

    model_8_2_flops->check( // {{{
      tb->tickcount(),

      tb->m_core->i_clk,
      tb->m_core->i_clk,
      tb->m_core->common_cg,

      tb->m_core->common_flush,
      tb->m_core->common_push,
      tb->m_core->common_pop,

      tb->m_core->fifo_8_2_flops_i_data,
      tb->m_core->fifo_8_2_flops_o_data,

      tb->m_core->fifo_8_2_flops_o_empty,
      tb->m_core->fifo_8_2_flops_o_full,

      tb->m_core->fifo_8_2_flops_o_pushed,
      tb->m_core->fifo_8_2_flops_o_popped,

      tb->m_core->fifo_8_2_flops_o_wrptr,
      tb->m_core->fifo_8_2_flops_o_rdptr,

      tb->m_core->fifo_8_2_flops_o_valid,
      tb->m_core->fifo_8_2_flops_o_nEntries,

      tb->m_core->fifo_8_2_flops_o_entries
    ); // }}}

    // Drivers evaluated at tickcount*10-2
    tb->m_core->common_cg   = (rand() % 100) != 0; // Drop i_cg 1/100.
    tb->m_core->common_flush = (rand() % 50) == 0; // Pulse i_flush high 1/50.
    tb->m_core->common_push = (rand() % 5) == 0; // Pulse i_push high 1/5.
    tb->m_core->common_pop  = (rand() % 6) == 0; // Pulse i_pop high 1/6.
    tb->m_core->common_data = rand();
    tb->m_core->fifo_8_8_mem_i_data = tb->m_core->common_data & 0xff;
    tb->m_core->fifo_1_2_mem_i_data = tb->m_core->common_data & 0x1;
    tb->m_core->fifo_5_5_mem_i_data = tb->m_core->common_data & 0x1f;
    tb->m_core->fifo_8_2_flops_i_data = tb->m_core->common_data & 0xff;
  }

  tb->closetrace();
  exit(EXIT_SUCCESS);
}

