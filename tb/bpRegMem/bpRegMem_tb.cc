
#include <stdio.h>
#include <stdlib.h>

#include "verilated.h"
#include "verilated_vcd_c.h"
#include "VerilatorTb.h"
#include "VbpRegMem_tb.h"
#include "bpRegMem_model.h"

#ifndef N_CYCLES
const int N_CYCLES = 100;
#endif

int main(int argc, char **argv, char **env) {

  Verilated::commandArgs(argc, argv);
  VerilatorTb<VbpRegMem_tb> *tb = new VerilatorTb<VbpRegMem_tb>();
  tb->opentrace("build/bpRegMem_tb.verilator.vcd");
  //tb->m_trace->dump(0); // Initialize waveform at beginning of time.

  // Instance models to compare against the tb.
  BpRegMemModel* model_64   = new BpRegMemModel(64);
  BpRegMemModel* model_2    = new BpRegMemModel(2);
  BpRegMemModel* model_128  = new BpRegMemModel(128);
  BpRegMemModel* model_5    = new BpRegMemModel(5);

  // Initialize simulation inputs
  tb->m_dut->common_cg = 0;
  tb->m_dut->common_bp_data = 0x55;
  tb->m_dut->common_bp_valid = 0;
  tb->m_dut->common_bp_ready = 0;
  tb->reset();

  // Run simulation for N_CYCLES clock periods.
  // check, drive, tick
  while (tb->tickcount() < N_CYCLES) {
    model_64->check( // {{{
      tb->tickcount(),

      tb->m_dut->i_clk,
      tb->m_dut->i_rst,
      tb->m_dut->common_cg,

      tb->m_dut->common_bp_data,
      tb->m_dut->common_bp_valid,
      tb->m_dut->bpRegMem_64_o_bp_ready,

      tb->m_dut->bpRegMem_64_o_bp_data,
      tb->m_dut->bpRegMem_64_o_bp_valid,
      tb->m_dut->common_bp_ready
    ); // }}}

    model_128->check( // {{{
      tb->tickcount(),

      tb->m_dut->i_clk,
      tb->m_dut->i_rst,
      tb->m_dut->common_cg,

      tb->m_dut->common_bp_data,
      tb->m_dut->common_bp_valid,
      tb->m_dut->bpRegMem_128_o_bp_ready,

      tb->m_dut->bpRegMem_128_o_bp_data,
      tb->m_dut->bpRegMem_128_o_bp_valid,
      tb->m_dut->common_bp_ready
    ); // }}}

    model_2->check( // {{{
      tb->tickcount(),

      tb->m_dut->i_clk,
      tb->m_dut->i_rst,
      tb->m_dut->common_cg,

      tb->m_dut->common_bp_data,
      tb->m_dut->common_bp_valid,
      tb->m_dut->bpRegMem_2_o_bp_ready,

      tb->m_dut->bpRegMem_2_o_bp_data,
      tb->m_dut->bpRegMem_2_o_bp_valid,
      tb->m_dut->common_bp_ready
    ); // }}}

    model_5->check( // {{{
      tb->tickcount(),

      tb->m_dut->i_clk,
      tb->m_dut->i_rst,
      tb->m_dut->common_cg,

      tb->m_dut->common_bp_data,
      tb->m_dut->common_bp_valid,
      tb->m_dut->bpRegMem_5_o_bp_ready,

      tb->m_dut->bpRegMem_5_o_bp_data,
      tb->m_dut->bpRegMem_5_o_bp_valid,
      tb->m_dut->common_bp_ready
    ); // }}}

    // Drivers evaluated at tickcount*10-2
    tb->m_dut->common_cg = 1; // TODO (rand() % 100) != 0; // Drop i_cg 1/100.
    tb->m_dut->common_bp_data = rand() & 0xff;
    tb->m_dut->common_bp_valid = (rand() % 5) == 0; // Pulse i_bp_valid 1/5.
    tb->m_dut->common_bp_ready = 1; // TODO (rand() % 6) != 0; // Drop i_bp_ready 1/6.

    tb->tick(); // Checks performed at negedge times.
  }

  tb->closetrace();
  exit(EXIT_SUCCESS);
}

