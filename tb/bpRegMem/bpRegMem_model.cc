
#include <stdio.h>

#include "bpRegMem_model.h"
#include "modelPrint.h"

BpRegMemModel::BpRegMemModel (unsigned int n) {
    nReg = n;
}

char * BpRegMemModel::info() {

    sprintf(infobuff,
        "BpRegMemModel__%d",
        nReg);

    return infobuff;
}

void BpRegMemModel::check(
    int unsigned t, // tickcount

    int unsigned i_clk,
    int unsigned i_rst,
    int unsigned i_cg,

    int unsigned i_bp_data,
    int unsigned i_bp_valid,
    int unsigned o_bp_ready,

    int unsigned o_bp_data,
    int unsigned o_bp_valid,
    int unsigned i_bp_ready
) {
  if (i_rst) {
    modelPrint(WARN, t, info(),
        "Calling check() when i_rst is asserted. Nothing checked.");
    return;
  }

  ///////////////////////////////////////////////////////////////////////////
  // Model behaviour
  ///////////////////////////////////////////////////////////////////////////

  bool writeNotRead = (i_bp_data & (1 << 7)) != 0;
  bool inAccepted = i_bp_valid && o_bp_ready;
  bool outAccepted = o_bp_valid && i_bp_ready;
  bool txnBegin = !wr && inAccepted;
  bool wrBegin = txnBegin && writeNotRead;
  bool wrEnd = wr && inAccepted;
  bool rdBegin = (txnBegin && !writeNotRead) || wrEnd;
  bool rdEnd = rd && outAccepted;

  unsigned int model_o_bp_data = rdData;
  bool model_o_bp_valid = rd;
  bool model_o_bp_ready = i_bp_ready;

  bool doDataCheck = false;

  if (i_cg) {

    if (rdBegin) {
      for (int i=0; i < nReg; i++) {
        if (i == addr) {
          rdData = regs[i];
          doDataCheck = isKnown[i];
          break;
        }
      }
      rd = true;
    } else if (rdEnd) {
      rd = rdBegin; // Allow back-to-back reads.
    }

    if (wrBegin) {
      wr = true;
    } else if (wrEnd) {
      for (int i=0; i < nReg; i++) {
        if (i == addr) {
          regs[i] = i_bp_data;
          isKnown[i] = true;
          break;
        }
      }
      wr = false; // No back-to-back writes.
    }

    if (txnBegin) {
      addr = i_bp_data & 0x7f;
    }
  }

  ///////////////////////////////////////////////////////////////////////////
  // Check state
  ///////////////////////////////////////////////////////////////////////////

  /*
  if (doDataCheck && (model_o_bp_data != o_bp_data)) {
    modelPrint(ERROR, t, info(),
      "o_bp_data model=%d; design=%d",
      model_o_bp_data, o_bp_data);
  }

  if (model_o_bp_valid != o_bp_valid) {
    modelPrint(ERROR, t, info(),
      "o_bp_valid model=%d; design=%d",
      model_o_bp_valid, o_bp_valid);
  }
  */

  if (model_o_bp_ready != o_bp_ready) {
    modelPrint(ERROR, t, info(),
      "o_bp_ready model=%d; design=%d",
      model_o_bp_ready, o_bp_ready);
  }
}

