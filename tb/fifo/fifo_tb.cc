
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
  tb->reset();

  // Run simulation for N_CYCLES clock periods.
  while (tb->tickcount() < N_CYCLES) {

    model_8_8_mem->check( // {{{
      tb->tickcount(),

      tb->m_dut->i_clk,
      tb->m_dut->i_clk,
      tb->m_dut->common_cg,

      tb->m_dut->common_flush,
      tb->m_dut->common_push,
      tb->m_dut->common_pop,

      tb->m_dut->fifo_8_8_mem_i_data,
      tb->m_dut->fifo_8_8_mem_o_data,

      tb->m_dut->fifo_8_8_mem_o_empty,
      tb->m_dut->fifo_8_8_mem_o_full,

      tb->m_dut->fifo_8_8_mem_o_pushed,
      tb->m_dut->fifo_8_8_mem_o_popped,

      tb->m_dut->fifo_8_8_mem_o_wrptr,
      tb->m_dut->fifo_8_8_mem_o_rdptr,

      tb->m_dut->fifo_8_8_mem_o_valid,
      tb->m_dut->fifo_8_8_mem_o_nEntries,

      tb->m_dut->fifo_8_8_mem_o_entries
    ); // }}}

    model_1_2_mem->check( // {{{
      tb->tickcount(),

      tb->m_dut->i_clk,
      tb->m_dut->i_clk,
      tb->m_dut->common_cg,

      tb->m_dut->common_flush,
      tb->m_dut->common_push,
      tb->m_dut->common_pop,

      tb->m_dut->fifo_1_2_mem_i_data,
      tb->m_dut->fifo_1_2_mem_o_data,

      tb->m_dut->fifo_1_2_mem_o_empty,
      tb->m_dut->fifo_1_2_mem_o_full,

      tb->m_dut->fifo_1_2_mem_o_pushed,
      tb->m_dut->fifo_1_2_mem_o_popped,

      tb->m_dut->fifo_1_2_mem_o_wrptr,
      tb->m_dut->fifo_1_2_mem_o_rdptr,

      tb->m_dut->fifo_1_2_mem_o_valid,
      tb->m_dut->fifo_1_2_mem_o_nEntries,

      tb->m_dut->fifo_1_2_mem_o_entries
    ); // }}}

    model_5_5_mem->check( // {{{
      tb->tickcount(),

      tb->m_dut->i_clk,
      tb->m_dut->i_clk,
      tb->m_dut->common_cg,

      tb->m_dut->common_flush,
      tb->m_dut->common_push,
      tb->m_dut->common_pop,

      tb->m_dut->fifo_5_5_mem_i_data,
      tb->m_dut->fifo_5_5_mem_o_data,

      tb->m_dut->fifo_5_5_mem_o_empty,
      tb->m_dut->fifo_5_5_mem_o_full,

      tb->m_dut->fifo_5_5_mem_o_pushed,
      tb->m_dut->fifo_5_5_mem_o_popped,

      tb->m_dut->fifo_5_5_mem_o_wrptr,
      tb->m_dut->fifo_5_5_mem_o_rdptr,

      tb->m_dut->fifo_5_5_mem_o_valid,
      tb->m_dut->fifo_5_5_mem_o_nEntries,

      tb->m_dut->fifo_5_5_mem_o_entries
    ); // }}}

    model_8_2_flops->check( // {{{
      tb->tickcount(),

      tb->m_dut->i_clk,
      tb->m_dut->i_clk,
      tb->m_dut->common_cg,

      tb->m_dut->common_flush,
      tb->m_dut->common_push,
      tb->m_dut->common_pop,

      tb->m_dut->fifo_8_2_flops_i_data,
      tb->m_dut->fifo_8_2_flops_o_data,

      tb->m_dut->fifo_8_2_flops_o_empty,
      tb->m_dut->fifo_8_2_flops_o_full,

      tb->m_dut->fifo_8_2_flops_o_pushed,
      tb->m_dut->fifo_8_2_flops_o_popped,

      tb->m_dut->fifo_8_2_flops_o_wrptr,
      tb->m_dut->fifo_8_2_flops_o_rdptr,

      tb->m_dut->fifo_8_2_flops_o_valid,
      tb->m_dut->fifo_8_2_flops_o_nEntries,

      tb->m_dut->fifo_8_2_flops_o_entries
    ); // }}}

    tb->tick(); // Checks performed at negedge times.
  }

  tb->closetrace();
  exit(EXIT_SUCCESS);
}

