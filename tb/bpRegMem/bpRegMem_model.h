#ifndef BPREGMEM_MODEL_H_
#define BPREGMEM_MODEL_H_

class BpRegMemModel {
    private:
        static const int unsigned INFO_BUFFLEN = 128;
        static const int unsigned MAX_N_REG = 128;

        int unsigned nReg;

        char infobuff[INFO_BUFFLEN];

        bool rd = false;
        bool wr = false;
        int unsigned addr = 0;
        int unsigned rdData = 0;
        int unsigned regs[MAX_N_REG] = {0};
        bool isKnown[MAX_N_REG] = {0};

    public:
        BpRegMemModel(unsigned int n);
        char * info();
        void check(
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
        );
};

#endif // BPREGMEM_MODEL_H_

