
#include <stdio.h>

#include "fifo_model.h"
#include "fifo_utils.h"

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
    data_mask = (width == 32) ? 0xffffffff : ((1 << width) - 1);
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

void FifoModel::flush() {
    rd_ptr = 0;
    wr_ptr = 0;
    nEntries = 0;
}

int unsigned FifoModel::pop() {
    int unsigned front = entries[rd_ptr];
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

    return front;
}

void FifoModel::push(unsigned int back) {
    entries[wr_ptr] = back & data_mask;
    nEntries++;

    if (topology == CIRCULAR) {
        // Pushing doesn't move read pointer.

        // Pushing doesn't move data.

        // Wrap around write pointer.
        wr_ptr = (wr_ptr == (depth-1)) ? 0 : (wr_ptr + 1);
    } else if (topology == LINEAR) {
        // Pushing doesn't move read pointer.

        // Pushing doesn't move data.

        // Increment write pointer.
        wr_ptr = nEntries-1;
    }
}

int unsigned FifoModel::getWidth() {
    return width;
}

int unsigned FifoModel::getDepth() {
    return depth;
}

int unsigned FifoModel::getNEntries() {
    return nEntries;
}

int unsigned FifoModel::getDataMask() {
    return data_mask;
}

int unsigned FifoModel::getEntry(int unsigned index) {
    return entries[index];
}

bool FifoModel::isEmpty() {
    return (nEntries == 0);
}

bool FifoModel::isFull() {
    return (nEntries >= depth);
}

int unsigned FifoModel::popcnt(int unsigned o_valid) {
    int unsigned ret = 0;
    for (int i = 0; i < depth; i++) {
        if (o_valid & (1 << i)) ret++;
    }
    return ret;
}


void FifoModel::check(
    int unsigned t, // tickcount

    int unsigned i_clk,
    int unsigned i_rst,
    int unsigned i_cg,

    int unsigned i_flush,
    int unsigned i_push,
    int unsigned i_pop,

    int unsigned i_data,
    int unsigned o_data,

    int unsigned o_empty,
    int unsigned o_full,

    int unsigned o_pushed,
    int unsigned o_popped,

    int unsigned o_wrptr,
    int unsigned o_rdptr,

    int unsigned o_valid,
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

  if (i_cg) {
    bool _isEmpty = isEmpty();
    bool _isFull = isFull();

    // Pop-then-push ordering is important.

    if (i_flush)
      flush();

    if (!_isEmpty && i_pop && !i_flush)
      pop();

    if (!_isFull && i_push && !i_flush)
      push(i_data);
  }

  ///////////////////////////////////////////////////////////////////////////
  // Check state
  ///////////////////////////////////////////////////////////////////////////

  if (isEmpty() != (bool)o_empty) {
    modelPrint(ERROR, t, info(),
      "model: isEmpty=%d; design: o_empty=%d",
      isEmpty(), o_empty);
  }

  if (isFull() != (bool)o_full) {
    modelPrint(ERROR, t, info(),
      "model: isFull=%d; design: o_full=%d",
      isFull(), o_full);
  }

  if (4 > depth && nEntries != popcnt(o_valid)) {
    modelPrint(ERROR, t, info(),
      "model: nEntries=%d; design: popcnt(o_valid)=%d o_valid=0x%x",
      nEntries, popcnt(o_valid), o_valid);
  }

  if (depth >= 4 && nEntries != o_nEntries) {
    modelPrint(ERROR, t, info(),
      "model: nEntries=%d; design: o_nEntries=%d",
      nEntries, o_nEntries);
  }

  if ((o_data != getEntry(rd_ptr)) && !isEmpty()) {
    modelPrint(ERROR, t, info(),
      "model: getEntry(rd_ptr)=%x; design: o_data=%x",
      getEntry(rd_ptr), o_data);

    for (int i=0; i < depth; i++) {
      modelPrint(WARN, t, info(),
        "entry%d=%x",
        i, getEntry(i));
    }
  }
}

