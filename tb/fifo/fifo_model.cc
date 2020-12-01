
#include <stdio.h>

#include "fifo_model.h"
#include "modelPrint.h"

FifoModel::FifoModel (unsigned int w,
                      unsigned int d,
                      FifoModel_topology topo,
                      FifoModel_storage stor) {
    width = w;
    depth = d;
    topology = topo;
    storage = stor;

    wr_ptr = 0;
    rd_ptr = 0;
    nEntries = 0;

    // This is just a verif model so only support up to 32b data width.
    dataMask = (width == 32) ? 0xffffffff : ((1 << width) - 1);
}

char * FifoModel::info() {
    const char * topologies[] = {"CIRCULAR", "LINEAR"};
    const char * stores[] = {"MEMORY", "FLOPS"};

    sprintf(infobuff,
        "FifoModel__%d_%d_%s_%s",
        width,
        depth,
        topologies[topology],
        stores[storage]);

    return infobuff;
}

int unsigned FifoModel::popcnt(int unsigned o_validEntries) {
    int unsigned ret = 0;
    for (int i = 0; i < depth; i++) {
        if (o_validEntries & (1 << i)) ret++;
    }
    return ret;
}


void FifoModel::check(
    int unsigned t, // tickcount

    int unsigned i_clk,
    int unsigned i_rst,
    int unsigned i_cg,

    int unsigned i_flush,

    int unsigned i_data,
    int unsigned i_valid, // push
    int unsigned o_ready, // !full

    int unsigned o_data,
    int unsigned o_valid, // !empty
    int unsigned i_ready, // pop

    int unsigned o_pushed,
    int unsigned o_popped,

    int unsigned o_wrptr,
    int unsigned o_rdptr,

    int unsigned o_validEntries,
    int unsigned o_nEntries,

    int unsigned o_entries
) {
  if (i_rst) {
    modelPrint(WARN, t, info(),
        "Calling check() when i_rst is asserted. Nothing checked.");
    return;
  }

  ///////////////////////////////////////////////////////////////////////////
  // Model behaviour
  ///////////////////////////////////////////////////////////////////////////
  bool empty = (nEntries == 0);
  bool full = (nEntries >= depth);
  int unsigned model_head = entries[rd_ptr];
  int unsigned model_nEntries = nEntries;

  // Pop-then-push ordering is important.
  if (i_cg) {

    if (i_flush) {
      rd_ptr = 0;
      wr_ptr = 0;
      nEntries = 0;
    }

    if (!empty && i_ready && !i_flush) {
      nEntries--;

      if (topology == CIRCULAR) {
          // Wrap around read pointer.
          rd_ptr = (rd_ptr == (depth-1)) ? 0 : (rd_ptr + 1);
          // Data stays where it is.
          // Write pointer doesn't change.
      } else if (topology == LINEAR) {
          // Read pointer is fixed to 0.
          // Shuffle data down.
          for (int i = 0; i < nEntries; i++) {
              entries[i] = entries[i+1];
          }
          // Write pointer moves down to match data.
          wr_ptr--;
      }
    }

    if (!full && i_valid && !i_flush) {
      entries[wr_ptr] = i_data & dataMask;
      nEntries++;

      // Pushing doesn't modify read pointer, or move data.
      if (topology == CIRCULAR) {
          // Wrap around write pointer.
          wr_ptr = (wr_ptr == (depth-1)) ? 0 : (wr_ptr + 1);
      } else if (topology == LINEAR) {
          // Increment write pointer.
          wr_ptr = nEntries-1;
      }
    }

  }

  ///////////////////////////////////////////////////////////////////////////
  // Check state
  ///////////////////////////////////////////////////////////////////////////

  if (empty == (bool)o_valid) {
    modelPrint(ERROR, t, info(), "empty model=%d design=%d",
      empty, o_valid);
  }

  if (full == (bool)o_ready) {
    modelPrint(ERROR, t, info(), "full model=%d design=%d",
      full, o_ready);
  }

  if (4 > depth && model_nEntries != popcnt(o_validEntries)) {
    modelPrint(ERROR, t, info(), "nEntries model=%d design=%d o_validEntries=0x%x",
      model_nEntries, popcnt(o_validEntries), o_validEntries);
  } else if (4 <= depth && model_nEntries != o_nEntries) {
    modelPrint(ERROR, t, info(), "nEntries model=%d design=%d",
      model_nEntries, o_nEntries);
  }

  if ((model_head != o_data) && !empty) {
    modelPrint(ERROR, t, info(), "head model=%x design=%x",
      model_head, o_data);

    for (int i=0; i < depth; i++) {
      modelPrint(WARN, t, info(), "entry%d=%x",
        i, entries[i]);
    }
  }
}

