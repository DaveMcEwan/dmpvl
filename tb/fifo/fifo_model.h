#ifndef FIFO_MODEL_H_
#define FIFO_MODEL_H_

typedef enum {CIRCULAR, LINEAR} FifoModel_topology;
typedef enum {MEMORY, FLOPS} FifoModel_storage;

class FifoModel {
    private:
        static const int unsigned INFO_BUFFLEN = 128;
        static const int unsigned MAX_ENTRIES = 32;

        int unsigned width;
        int unsigned depth;
        FifoModel_topology topology;
        FifoModel_storage storage;

        char infobuff[INFO_BUFFLEN];

        int unsigned wr_ptr;
        int unsigned rd_ptr;
        int unsigned nEntries;
        int unsigned dataMask;
        int unsigned entries[MAX_ENTRIES];

    public:
        FifoModel(unsigned int w,
                  unsigned int d,
                  FifoModel_topology topo,
                  FifoModel_storage stor);
        char * info();
        void flush();
        int unsigned pop();
        void push(unsigned int back);
        int unsigned getWidth();
        int unsigned getDepth();
        int unsigned getNEntries();
        int unsigned getDataMask();
        int unsigned getEntry(int unsigned index);
        bool isEmpty();
        bool isFull();
        int unsigned popcnt(int unsigned o_validEntries);
        void check(
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

            int unsigned o_wptr,
            int unsigned o_rptr,

            int unsigned o_validEntries,
            int unsigned o_nEntries,

            int unsigned o_entries
        );
};

#endif // FIFO_MODEL_H_

