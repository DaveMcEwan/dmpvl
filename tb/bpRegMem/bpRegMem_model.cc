
#include <assert.h>
#include <stdio.h>

#include "bpRegMem_model.h"
#include "modelPrint.h"

BpRegMemModel::BpRegMemModel (unsigned int n, unsigned int v) {
    nReg = n;
    value0 = v;
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

  bool cmdWr = (i_bp_data & (1 << 7)) != 0;
  bool cmdRd = (i_bp_data & (1 << 7)) == 0;
  unsigned int cmdAddr = i_bp_data & 0x7f;

  bool txnBegin = !wr && inAccepted;
  bool inBurst = (0 != burst) && (0 != addr);
  bool inBurstWr = inBurst && wr;
  bool inBurstRd = inBurst && rd;
  bool doWrite = wr && inAccepted;
  //modelPrint(NOTE, t, info(), "txnBegin=%d cmdWr=%d", txnBegin, cmdWr);
  //modelPrint(NOTE, t, info(), "inBurst=%d inBurstWr=%d inBurstRd=%d", inBurst, inBurstWr, inBurstRd);

  bool wrSet = txnBegin && cmdWr;
  bool wrClr = doWrite && !inBurst;
  //modelPrint(NOTE, t, info(), "wrSet=%d wrClr=%d", wrSet, wrClr);
  bool rdSet = (txnBegin && cmdRd) || wrClr;
  bool rdClr = outAccepted && !inBurst;
  //modelPrint(NOTE, t, info(), "rdSet=%d rdClr=%d", rdSet, rdClr);
  bool burstInit = doWrite && (addr == 0);
  bool burstDecr = (inBurstWr && inAccepted) || (inBurstRd && outAccepted);
  //modelPrint(NOTE, t, info(), "burstInit=%d burstDecr=%d", burstInit, burstDecr);


  unsigned int model_o_bp_data = rdData;
  bool model_o_bp_valid = rd;
  //modelPrint(NOTE, t, info(), "model_o_bp_data=%x o_bp_data=%x", model_o_bp_data, o_bp_data);
  //modelPrint(NOTE, t, info(), "model_o_bp_valid=%d o_bp_valid=%d", model_o_bp_valid, o_bp_valid);

  bool model_o_bp_ready = i_bp_ready && !inBurstRd;
  //modelPrint(NOTE, t, info(), "rd=%d wr=%d addr=%d rdData=%x", rd, wr, addr, rdData);

  bool doDataCheck = false;

  isKnown[0] = true;

  if (i_cg) {

    if (rdSet || (rd && !rdClr)) {
      rdData = 0;
      if (0 == addr) {
          rdData = value0;
      } else {
        for (int i=0; i < nReg; i++) {
          if ((i+startAddr) == addr) {
            rdData = regs[i];
            break;
          }
        }
      }
    } else if (rdClr) {
      doDataCheck = isKnown[addr];
    }

    if (doWrite) {
      for (int i=0; i < nReg; i++) {
        if ((i+startAddr) == addr) {
          regs[i] = i_bp_data & 0xff;
          isKnown[i] = true;
          break;
        }
      }
    }

    if (burstInit) {
      burst = i_bp_data & 0xff;
    } else if (burstDecr) {
      burst -= 1;
    }
    assert(0 <= burst < 256);

    if (rdSet) {
      rd = true;
    } else if (rdClr) {
      rd = false;
    }

    if (wrSet) {
      wr = true;
    } else if (wrClr) {
      wr = false;
    }

    if (txnBegin) {
      addr = cmdAddr;
    }
    assert(0 <= addr < 128);

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

