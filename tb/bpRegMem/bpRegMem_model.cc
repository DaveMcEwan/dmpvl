
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
  //modelPrint(NOTE, t, info(), "i_bp_valid=%d i_bp_data=%x", i_bp_valid, i_bp_data);

  ///////////////////////////////////////////////////////////////////////////
  // Model behaviour
  ///////////////////////////////////////////////////////////////////////////

  bool inAccepted = i_bp_valid && o_bp_ready;
  bool outAccepted = o_bp_valid && i_bp_ready;
  //modelPrint(NOTE, t, info(), "inAccepted=%d outAccepted=%d", inAccepted, outAccepted);

  bool txnBegin = !wr && inAccepted;
  bool writeNotRead = (i_bp_data & (1 << 7)) != 0;
  //modelPrint(NOTE, t, info(), "txnBegin=%d writeNotRead=%d", txnBegin, writeNotRead);

  bool wrBegin = txnBegin && writeNotRead;
  bool wrEnd = wr && inAccepted;
  //modelPrint(NOTE, t, info(), "wrBegin=%d wrEnd=%d", wrBegin, wrEnd);

  bool rdBegin = (txnBegin && !writeNotRead) || wrEnd;
  bool rdEnd = rd && outAccepted;
  //modelPrint(NOTE, t, info(), "rdBegin=%d rdEnd=%d", rdBegin, rdEnd);


  unsigned int model_o_bp_data = rdData;
  bool model_o_bp_valid = rd;
  bool model_o_bp_ready = i_bp_ready;
  //modelPrint(NOTE, t, info(), "model_o_bp_data=%x o_bp_data=%x", model_o_bp_data, o_bp_data);
  //modelPrint(NOTE, t, info(), "model_o_bp_valid=%d o_bp_valid=%d", model_o_bp_valid, o_bp_valid);

  //modelPrint(NOTE, t, info(), "rd=%d wr=%d addr=%d rdData=%x", rd, wr, addr, rdData);

  bool doDataCheck = false;

  if (i_cg) {

    if (rdBegin) {
      rdData = 0;
      for (int i=0; i < nReg; i++) {
        if (i == addr) {
          rdData = regs[i];
          break;
        }
      }
      rd = true;
    } else if (rdEnd) {
      rd = rdBegin; // Allow back-to-back reads.
      doDataCheck = isKnown[addr];
    }

    if (wrBegin) {
      wr = true;
    } else if (wrEnd) {
      for (int i=0; i < nReg; i++) {
        if (i == addr) {
          regs[i] = i_bp_data & 0xff;
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

  if (doDataCheck && (model_o_bp_data != o_bp_data)) {
    modelPrint(ERROR, t, info(),
      "o_bp_data model=%x; design=%x",
      model_o_bp_data, o_bp_data);
  }

  if (model_o_bp_valid != o_bp_valid) {
    modelPrint(ERROR, t, info(),
      "o_bp_valid model=%d; design=%d",
      model_o_bp_valid, o_bp_valid);
  }

  if (model_o_bp_ready != o_bp_ready) {
    modelPrint(ERROR, t, info(),
      "o_bp_ready model=%d; design=%d",
      model_o_bp_ready, o_bp_ready);
  }

  //for (int i=0; i < nReg; i++) {
  //  modelPrint(NOTE, t, info(),
  //    "model reg[%d]=%x", i, regs[i]);
  //}

  //printf("\n");
}

