/* rsm_hier.v
RV32I_Zicsr_Zifencei implemented in Verilog2001 as hierarchical modules.
*/

`default_nettype none

`define TRAP_VECTOR 32'h0000_0010
`define RESET_VECTOR 32'h0000_0000
`define XLEN 32
`define XLEN_R 31:0
`define AXI_ADDR_W 32
`define AXI_DATA_W 32

// {{{ ff macros

// ClockGate currently defined as: inferred from if condition
// Reset currently defined as: synchronous, active-low

// no clockgate, reset
// E.g: `ff_nocg_rst (reg [9:0], foo, 10'd0)
`define ff_nocg_rst(t, n, rstval) \
    t n``_d, n``_q; \
    always @ (posedge i_clk) \
      if (!i_rstn) n``_q <= rstval; \
      else n``_q <= n``_d;

// clockgate, no reset
// E.g: `ff_cg_norst (reg [9:0], foo, i_cg)
`define ff_cg_norst(t, n, cg) \
    t n``_d, n``_q; \
    always @ (posedge i_clk) \
      if (cg) n``_q <= n``_d; \
      else n``_q <= n``_q;

// clockgate, reset
// E.g: `ff_cg_rst (reg [9:0], foo, i_cg, 10'd0)
`define ff_cg_rst(t, n, cg, rstval) \
    t n``_d, n``_q; \
    always @ (posedge i_clk) \
      if (!i_rstn) n``_q <= rstval; \
      else if (cg) n``_q <= n``_d; \
      else n``_q <= n``_q;

// }}} ff macros

module ifu_m ( // {{{ Instruction Fetch Unit
  input wire i_clk,
  input wire i_rstn,

  // AXI Read address channel signals.
  output wire [`AXI_ADDR_W-1:0] o_axi_araddr,
  output wire [2:0]             o_axi_arprot,
  output wire                   o_axi_arvalid,
  input  wire                   i_axi_arready,

  // AXI Read data channel signals.
  input  wire [`AXI_DATA_W-1:0] i_axi_rdata,
  input  wire [1:0]             i_axi_rresp,
  input  wire                   i_axi_rvalid,
  output wire                   o_axi_rready,

  input wire i_execute,
  input wire i_fencei,
  output wire o_ifucomplete, // Only used for FENCEI.
  output wire o_ifutrap, // Synthesise a trap on AXI SLVERR or DECERR.

  input wire i_fetch,       // Fetch request validator
  input wire [31:0]  i_pc,  // PC address to fetch

  output wire [31:0] o_ir,      // Instruction Register
  output wire        o_ir_valid // First cycle validator
);

assign o_ifucomplete = i_execute && i_fencei;

assign o_axi_araddr = {i_pc[31:2], 2'd0}; // AXI address always word-aligned.
assign o_axi_arprot = 3'b110; // Instruction, Non-secure, Unpriviliged.

wire axi_ar = (i_axi_arready && o_axi_arvalid);

`ff_nocg_rst(reg, arvalid, 1'b0)
always @*
  if (i_fetch)     arvalid_d = 1'b1;
  else if (axi_ar) arvalid_d = 1'b0;
  else             arvalid_d = arvalid_q;

assign o_axi_arvalid = arvalid_q;

assign o_axi_rready = 1'b1; // Always accept.

wire axi_r = (o_axi_rready && i_axi_rvalid);

assign o_ifutrap = axi_r && i_axi_rresp[1];

`ff_cg_norst(reg [31:0], ir, axi_r)
always @* ir_d = i_axi_rdata;

`ff_nocg_rst(reg, ir_valid, 1'b0)
always @* ir_valid_d = axi_r && !i_axi_rresp[1] && !ir_valid_q;

assign o_ir = ir_q;
assign o_ir_valid = ir_valid_q;

endmodule // }}} ifu_m

module dec_m ( // {{{ Instruction Decode Unit
  input wire i_clk,
  input wire i_rstn,

  input wire [31:0] i_ir,       // Instruction Register
  input wire        i_ir_valid, // First cycle validator

  // ifu
  output wire o_fencei,

  // bra
  output wire o_jal,
  output wire o_jalr,
  output wire o_beq,
  output wire o_bne,
  output wire o_blt,
  output wire o_bge,
  output wire o_bltu,
  output wire o_bgeu,
  output wire o_ecall,
  output wire o_ebreak,

  // csr
  output wire o_csrrw,
  output wire o_csrrs,
  output wire o_csrrc,
  output wire o_csrrwi,
  output wire o_csrrsi,
  output wire o_csrrci,

  // alu
  output wire o_lui,
  output wire o_auipc,
  output wire o_addi,
  output wire o_slti,
  output wire o_sltiu,
  output wire o_xori,
  output wire o_ori,
  output wire o_andi,
  output wire o_slli,
  output wire o_srli,
  output wire o_srai,
  output wire o_add,
  output wire o_sub,
  output wire o_sll,
  output wire o_slt,
  output wire o_sltu,
  output wire o_xor,
  output wire o_srl,
  output wire o_sra,
  output wire o_or,
  output wire o_and,

  // lsu
  output wire o_lb,
  output wire o_lh,
  output wire o_lw,
  output wire o_lbu,
  output wire o_lhu,
  output wire o_sb,
  output wire o_sh,
  output wire o_sw,
  output wire o_fence,

  output wire [11:0] o_iimm, // 11:0,  bra, alu, lsu
  output wire [11:0] o_simm, // 11:0,  lsu, (sb, sh, sw)
  output wire [12:0] o_bimm, // 12:1,  bra (beq, bne, blt, bge, bltu, bgeu)
  output wire [31:0] o_uimm, // 31:12, alu (lui, auipc)
  output wire [20:0] o_jimm, // 20:1,  bra (jal)
  output wire [4:0]  o_zimm, // 4:0,   csr

  output wire [3:0]  o_prec, // FENCE
  output wire [3:0]  o_succ, // FENCE

  // xrf
  output wire [4:0] o_rs1i,
  output wire [4:0] o_rs2i, // also shamt
  output wire [4:0] o_rdi,

  output wire o_execute,
  output wire o_dectrap
);

wire [6:0] opcode = i_ir[6:0];
wire [1:0] opcode2l = opcode[1:0];
wire [4:0] opcode5u = opcode[6:2];
wire [2:0] funct3 = i_ir[14:12];
wire [6:0] funct7 = i_ir[31:25];

// {{{ ff to outputs

`ff_cg_rst(reg, dec_fencei, i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_jal,    i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_jalr,   i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_beq,    i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_bne,    i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_blt,    i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_bge,    i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_bltu,   i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_bgeu,   i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_ecall,  i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_ebreak, i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_csrrw,  i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_csrrs,  i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_csrrc,  i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_csrrwi, i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_csrrsi, i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_csrrci, i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_lui,    i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_auipc,  i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_addi,   i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_slti,   i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_sltiu,  i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_xori,   i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_ori,    i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_andi,   i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_slli,   i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_srli,   i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_srai,   i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_add,    i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_sub,    i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_sll,    i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_slt,    i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_sltu,   i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_xor,    i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_srl,    i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_sra,    i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_or,     i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_and,    i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_lb,     i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_lh,     i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_lw,     i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_lbu,    i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_lhu,    i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_sb,     i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_sh,     i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_sw,     i_ir_valid, 1'b0)
`ff_cg_rst(reg, dec_fence,  i_ir_valid, 1'b0)

assign o_fencei = dec_fencei_q;
assign o_jal    = dec_jal_q;
assign o_jalr   = dec_jalr_q;
assign o_beq    = dec_beq_q;
assign o_bne    = dec_bne_q;
assign o_blt    = dec_blt_q;
assign o_bge    = dec_bge_q;
assign o_bltu   = dec_bltu_q;
assign o_bgeu   = dec_bgeu_q;
assign o_ecall  = dec_ecall_q;
assign o_ebreak = dec_ebreak_q;
assign o_csrrw  = dec_csrrw_q;
assign o_csrrs  = dec_csrrs_q;
assign o_csrrc  = dec_csrrc_q;
assign o_csrrwi = dec_csrrwi_q;
assign o_csrrsi = dec_csrrsi_q;
assign o_csrrci = dec_csrrci_q;
assign o_lui    = dec_lui_q;
assign o_auipc  = dec_auipc_q;
assign o_addi   = dec_addi_q;
assign o_slti   = dec_slti_q;
assign o_sltiu  = dec_sltiu_q;
assign o_xori   = dec_xori_q;
assign o_ori    = dec_ori_q;
assign o_andi   = dec_andi_q;
assign o_slli   = dec_slli_q;
assign o_srli   = dec_srli_q;
assign o_srai   = dec_srai_q;
assign o_add    = dec_add_q;
assign o_sub    = dec_sub_q;
assign o_sll    = dec_sll_q;
assign o_slt    = dec_slt_q;
assign o_sltu   = dec_sltu_q;
assign o_xor    = dec_xor_q;
assign o_srl    = dec_srl_q;
assign o_sra    = dec_sra_q;
assign o_or     = dec_or_q;
assign o_and    = dec_and_q;
assign o_lb     = dec_lb_q;
assign o_lh     = dec_lh_q;
assign o_lw     = dec_lw_q;
assign o_lbu    = dec_lbu_q;
assign o_lhu    = dec_lhu_q;
assign o_sb     = dec_sb_q;
assign o_sh     = dec_sh_q;
assign o_sw     = dec_sw_q;
assign o_fence  = dec_fence_q;

// }}} ff to outputs

always @* dec_lui_d   = (opcode5u == 5'b01101);
always @* dec_auipc_d = (opcode5u == 5'b00101);

always @* dec_jal_d  = (opcode5u == 5'b11011);
always @* dec_jalr_d = (opcode5u == 5'b11001) && (funct3 == 3'b000);

always @* dec_beq_d  = (opcode5u == 5'b11000) && (funct3 == 3'b000);
always @* dec_bne_d  = (opcode5u == 5'b11000) && (funct3 == 3'b001);
always @* dec_blt_d  = (opcode5u == 5'b11000) && (funct3 == 3'b100);
always @* dec_bge_d  = (opcode5u == 5'b11000) && (funct3 == 3'b101);
always @* dec_bltu_d = (opcode5u == 5'b11000) && (funct3 == 3'b110);
always @* dec_bgeu_d = (opcode5u == 5'b11000) && (funct3 == 3'b111);

always @* dec_lb_d  = (opcode5u == 5'b00000) && (funct3 == 3'b000);
always @* dec_lh_d  = (opcode5u == 5'b00000) && (funct3 == 3'b001);
always @* dec_lw_d  = (opcode5u == 5'b00000) && (funct3 == 3'b010);
always @* dec_lbu_d = (opcode5u == 5'b00000) && (funct3 == 3'b100);
always @* dec_lhu_d = (opcode5u == 5'b00000) && (funct3 == 3'b101);
always @* dec_sb_d  = (opcode5u == 5'b01000) && (funct3 == 3'b000);
always @* dec_sh_d  = (opcode5u == 5'b01000) && (funct3 == 3'b001);
always @* dec_sw_d  = (opcode5u == 5'b01000) && (funct3 == 3'b010);

always @* dec_addi_d  = (opcode5u == 5'b00100) && (funct3 == 3'b000);
always @* dec_slti_d  = (opcode5u == 5'b00100) && (funct3 == 3'b010);
always @* dec_sltiu_d = (opcode5u == 5'b00100) && (funct3 == 3'b011);
always @* dec_xori_d  = (opcode5u == 5'b00100) && (funct3 == 3'b100);
always @* dec_ori_d   = (opcode5u == 5'b00100) && (funct3 == 3'b110);
always @* dec_andi_d  = (opcode5u == 5'b00100) && (funct3 == 3'b111);

always @* dec_slli_d  = (opcode5u == 5'b00100) && (funct3 == 3'b001) && (funct7 == 7'd0);
always @* dec_srli_d  = (opcode5u == 5'b00100) && (funct3 == 3'b101) && (funct7 == 7'd0);
always @* dec_srai_d  = (opcode5u == 5'b00100) && (funct3 == 3'b101) && (funct7 == 7'b0100000);

always @* dec_add_d  = (opcode5u == 5'b01100) && (funct3 == 3'b000) && (funct7 == 7'd0);
always @* dec_sub_d  = (opcode5u == 5'b01100) && (funct3 == 3'b000) && (funct7 == 7'b0100000);
always @* dec_sll_d  = (opcode5u == 5'b01100) && (funct3 == 3'b001) && (funct7 == 7'd0);
always @* dec_slt_d  = (opcode5u == 5'b01100) && (funct3 == 3'b010) && (funct7 == 7'd0);
always @* dec_sltu_d = (opcode5u == 5'b01100) && (funct3 == 3'b011) && (funct7 == 7'd0);
always @* dec_xor_d  = (opcode5u == 5'b01100) && (funct3 == 3'b100) && (funct7 == 7'd0);
always @* dec_srl_d  = (opcode5u == 5'b01100) && (funct3 == 3'b101) && (funct7 == 7'd0);
always @* dec_sra_d  = (opcode5u == 5'b01100) && (funct3 == 3'b101) && (funct7 == 7'b0100000);
always @* dec_or_d   = (opcode5u == 5'b01100) && (funct3 == 3'b110) && (funct7 == 7'd0);
always @* dec_and_d  = (opcode5u == 5'b01100) && (funct3 == 3'b111) && (funct7 == 7'd0);

always @* dec_fence_d = (opcode5u == 5'b00011) && (funct3 == 3'b000)
  && (o_rdi == 5'd0 && (o_rs1i == 5'd0)) && (i_ir[31:28] == 4'd0);

always @* dec_fencei_d = (opcode5u == 5'b00011) && (funct3 == 3'b001)
  && (o_rdi == 5'd0 && (o_rs1i == 5'd0)) && (o_iimm == 12'd0);

always @* dec_ecall_d = (opcode5u == 5'b11100) && (funct3 == 3'b000)
  && (o_rdi == 5'd0 && (o_rs1i == 5'd0)) && (o_iimm == 12'd0);

always @* dec_ebreak_d = (opcode5u == 5'b11100) && (funct3 == 3'b000)
  && (o_rdi == 5'd0 && (o_rs1i == 5'd0)) && (o_iimm == 12'd1);

always @* dec_csrrw_d = (opcode5u == 5'b11100) && (funct3 == 3'b001);
always @* dec_csrrs_d = (opcode5u == 5'b11100) && (funct3 == 3'b010);
always @* dec_csrrc_d = (opcode5u == 5'b11100) && (funct3 == 3'b011);
always @* dec_csrrwi_d = (opcode5u == 5'b11100) && (funct3 == 3'b101);
always @* dec_csrrsi_d = (opcode5u == 5'b11100) && (funct3 == 3'b110);
always @* dec_csrrci_d = (opcode5u == 5'b11100) && (funct3 == 3'b111);

assign o_iimm = i_ir[31:20];
assign o_simm = {i_ir[31:25], i_ir[11:7]};
assign o_bimm = {i_ir[31], i_ir[7], i_ir[30:25], i_ir[11:8], 1'b0};
assign o_uimm = {i_ir[31:12], 12'b0};
assign o_jimm = {i_ir[31], i_ir[19:12], i_ir[20], i_ir[30:21], 1'b0};
assign o_zimm = i_ir[19:15];

assign o_prec = i_ir[27:24];
assign o_succ = i_ir[23:20];

assign o_rs1i = i_ir[19:15];
assign o_rs2i = i_ir[24:20];
assign o_rdi = i_ir[11:7];

// Fixed 1 cycle calculation.
`ff_nocg_rst(reg, decode, 1'b0)
always @* decode_d = i_ir_valid;

// 1 cycle after IR is presented to dec_m, exactly one of the instruction
// outputs should assert, or o_dectrap should assert.
assign o_execute = decode_q && (dec_fencei_q
                             || dec_jal_q
                             || dec_jalr_q
                             || dec_beq_q
                             || dec_bne_q
                             || dec_blt_q
                             || dec_bge_q
                             || dec_bltu_q
                             || dec_bgeu_q
                             || dec_ecall_q
                             || dec_ebreak_q
                             || dec_csrrw_q
                             || dec_csrrs_q
                             || dec_csrrc_q
                             || dec_csrrwi_q
                             || dec_csrrsi_q
                             || dec_csrrci_q
                             || dec_lui_q
                             || dec_auipc_q
                             || dec_addi_q
                             || dec_slti_q
                             || dec_sltiu_q
                             || dec_xori_q
                             || dec_ori_q
                             || dec_andi_q
                             || dec_slli_q
                             || dec_srli_q
                             || dec_srai_q
                             || dec_add_q
                             || dec_sub_q
                             || dec_sll_q
                             || dec_slt_q
                             || dec_sltu_q
                             || dec_xor_q
                             || dec_srl_q
                             || dec_sra_q
                             || dec_or_q
                             || dec_and_q
                             || dec_lb_q
                             || dec_lh_q
                             || dec_lw_q
                             || dec_lbu_q
                             || dec_lhu_q
                             || dec_sb_q
                             || dec_sh_q
                             || dec_sw_q
                             || dec_fence_q);

assign o_dectrap = decode_q && (!o_execute || opcode2l != 2'b11);

endmodule // }}} dec_m

module bra_m ( // {{{ Branch Unit
  input wire i_clk,
  input wire i_rstn,

  input wire i_ifucomplete,
  input wire i_csrcomplete,
  input wire i_alucomplete,
  input wire i_lsucomplete,

  input wire i_ifutrap,
  input wire i_dectrap,
  input wire i_csrtrap,
  input wire i_lsutrap,

  // dec
  input wire i_jal,
  input wire i_jalr,
  input wire i_beq,
  input wire i_bne,
  input wire i_blt,
  input wire i_bge,
  input wire i_bltu,
  input wire i_bgeu,
  input wire i_ecall,
  input wire i_ebreak,

  // dec, externally extended
  input wire [12:0]  i_bimm, // 12:1
  input wire [11:0]  i_iimm, // 11:0
  input wire [20:0]  i_jimm, // 20:1

  // xrf
  input wire [31:0]  i_rs1,
  input wire [31:0]  i_rs2,

  input wire i_execute,

  output wire         o_xwrite,
  output wire [31:0]  o_linkpc,

  output wire o_instret, // csr

  output wire         o_fetch,  // ifu
  output wire [31:0]  o_pc      // ifu, alu
);

wire cond_eq = (i_rs1 == i_rs2);
wire cond_lt = ($signed(i_rs1) < $signed(i_rs2));
wire cond_ltu = (i_rs1 < i_rs2);

wire cond_ne = !cond_eq;
wire cond_ge = !cond_lt;
wire cond_geu = !cond_ltu;

wire take_eq =  i_beq  && cond_eq;
wire take_ne =  i_bne  && cond_ne;
wire take_lt =  i_blt  && cond_lt;
wire take_ge =  i_bge  && cond_ge;
wire take_ltu = i_bltu && cond_ltu;
wire take_geu = i_bgeu && cond_geu;

wire take = i_execute && (take_eq
                       || take_ne
                       || take_lt
                       || take_ge
                       || take_ltu
                       || take_geu);

wire branch = i_execute && (i_beq
                         || i_bne
                         || i_blt
                         || i_bge
                         || i_bltu
                         || i_bgeu);

wire jal = i_execute && i_jal;

wire jalr = i_execute && i_jalr;

// Treat ecall and ebreak as software trap.
wire etrap = i_execute && (i_ecall
                        || i_ebreak);

wire trap = i_ifutrap
         || i_dectrap
         || i_csrtrap
         || i_lsutrap
         || etrap;

wire complete = i_ifucomplete
             || i_csrcomplete
             || i_alucomplete
             || i_lsucomplete;

wire [31:0] sext_bimm = {{19{i_bimm[12]}}, i_bimm};
wire [31:0] sext_iimm = {{20{i_iimm[11]}}, i_iimm};
wire [31:0] sext_jimm = {{11{i_jimm[20]}}, i_jimm};

wire [31:0] calcpc_next = pc_q + 32'd4;
wire [31:0] calcpc_jal = pc_q + sext_jimm;
wire [31:0] calcpc_jalr = (i_rs1 + sext_iimm) & {{31{1'b1}}, 1'b0};
wire [31:0] calcpc_branch = pc_q + sext_bimm;

`ff_nocg_rst(reg, fetch, 1'b1)
always @* fetch_d = complete
                 || branch
                 || jal
                 || jalr
                 || trap;

// Program Counter
`ff_cg_rst(reg [31:0], pc, fetch_d, `RESET_VECTOR)
always @*
  (* parallel_case *)
  case (1'b1)
    (trap):   pc_d = `TRAP_VECTOR;
    (take):   pc_d = calcpc_branch;
    (jal):    pc_d = calcpc_jal;
    (jalr):   pc_d = calcpc_jalr;
    default:  pc_d = calcpc_next; // (complete || (branch && !take))
  endcase

assign o_xwrite = jal || jalr; // Any jump writes back link register.
assign o_linkpc = calcpc_next;
assign o_pc = pc_q;
assign o_fetch = fetch_q;

assign o_instret = fetch_d;

endmodule // }}} bra_m

module csr_m ( // {{{ Control Status Registers
  input wire i_clk,
  input wire i_rstn,

  input wire i_csrrw,
  input wire i_csrrs,
  input wire i_csrrc,
  input wire i_csrrwi,
  input wire i_csrrsi,
  input wire i_csrrci,

  input wire [11:0] i_iimm,
  input wire [4:0] i_zimm,
  input wire [4:0] i_rdi,

  input wire [`XLEN_R] i_rs1,

  input wire  i_instret,

  output wire o_xwrite,
  output wire [`XLEN_R] o_csrval,

  input wire  i_execute,
  output wire o_csrcomplete,
  output wire o_csrtrap
);

wire csraddr_cycle    = (i_iimm == 12'hC00);
wire csraddr_time     = (i_iimm == 12'hC01);
wire csraddr_instret  = (i_iimm == 12'hC02);
wire csraddr_cycleh   = (i_iimm == 12'hC80);
wire csraddr_timeh    = (i_iimm == 12'hC81);
wire csraddr_instreth = (i_iimm == 12'hC82);

// cycle register is shared with time.
`ff_nocg_rst(reg [63:0], csr_cycle, 64'd0)
always @* csr_cycle_d = csr_cycle_q + 1;

`ff_nocg_rst(reg [63:0], csr_instret, 64'd0)
always @*
  if (i_instret) csr_instret_d = csr_instret_q + 1;
  else           csr_instret_d = csr_instret_q;

reg [`XLEN_R] read_value;
always @*
  (* parallel_case *)
  case (1'b1)
    (csraddr_cycle):    read_value = csr_cycle_q[31:0];
    (csraddr_time):     read_value = csr_cycle_q[31:0];
    (csraddr_instret):  read_value = csr_instret_q[31:0];
    (csraddr_cycleh):   read_value = csr_cycle_q[63:32];
    (csraddr_timeh):    read_value = csr_cycle_q[63:32];
    (csraddr_instreth): read_value = csr_instret_q[63:32];
    default:            read_value = `XLEN'd0;
  endcase

wire access_csr_reg = i_execute && (i_csrrw
                                 || i_csrrs
                                 || i_csrrc);

wire access_csr_imm = i_execute && (i_csrrwi
                                 || i_csrrsi
                                 || i_csrrci);

wire access_csr = access_csr_reg || access_csr_imm;

wire read_csr = access_csr && (i_rdi != 0);
wire set_csr = (i_csrrs && (i_rs1 != 0)) || (i_csrrsi && (i_zimm != 0));
wire clr_csr = (i_csrrc && (i_rs1 != 0)) || (i_csrrci && (i_zimm != 0));
wire write_csr = i_csrrw || i_csrrwi;
wire update_csr = write_csr
                || set_csr
                || clr_csr;

wire valid_csraddr = csraddr_cycle
                   || csraddr_time
                   || csraddr_instret
                   || csraddr_cycleh
                   || csraddr_timeh
                   || csraddr_instreth;

//reg [`XLEN_R] write_value;
//always @*
//  if (access_csr_reg) write_value = i_rs1;
//  else                write_value = {(`XLEN-3)'d0, i_zimm}; // access_csr_imm
//
//wire [`XLEN_R] set_value = write_value;   // OR with target
//wire [`XLEN_R] clr_value = ~write_value;  // AND with target

wire csrtrap = (access_csr && !valid_csraddr)
             || (access_csr && update_csr); // All registers are RO.

// Fixed 1 cycle calculation.
`ff_nocg_rst(reg, complete, 1'b0)
always @* complete_d = access_csr;

assign o_xwrite = complete_q && valid_csraddr && !csrtrap;
assign o_csrval = read_value;

assign o_csrcomplete = complete_q;
assign o_csrtrap = complete_q && csrtrap;

endmodule // }}} csr_m

module alu_m ( // {{{ Arithmetic Logic Unit
  input wire i_clk,
  input wire i_rstn,

  // dec
  input wire [11:0] i_iimm, // 11:0
  input wire [31:0] i_uimm, // 31:12 (lui, auipc)

  input wire i_lui,
  input wire i_auipc,
  input wire i_addi,
  input wire i_slti,
  input wire i_sltiu,
  input wire i_xori,
  input wire i_ori,
  input wire i_andi,
  input wire i_slli,
  input wire i_srli,
  input wire i_srai,
  input wire i_add,
  input wire i_sub,
  input wire i_sll,
  input wire i_slt,
  input wire i_sltu,
  input wire i_xor,
  input wire i_srl,
  input wire i_sra,
  input wire i_or,
  input wire i_and,

  // bra
  input wire [31:0] i_pc,

  // xrf
  input wire [`XLEN_R] i_rs1,
  input wire [`XLEN_R] i_rs2,

  // No ALU instructions cause trap.
  input wire i_execute,
  output wire o_complete,
  output wire o_xwrite,
  output wire [`XLEN_R] o_result
);

wire [`XLEN_R] sext_iimm = {{(`XLEN-12){i_iimm[11]}}, i_iimm};
wire [4:0] shamt = i_iimm[4:0];

wire [`XLEN_R] calc_lui = i_uimm;
wire [`XLEN_R] calc_auipc = i_uimm + i_pc;
wire [`XLEN_R] calc_addi = i_rs1 + sext_iimm;
wire [`XLEN_R] calc_slti = {{31{1'b0}}, ($signed(i_rs1) < $signed(sext_iimm))};
wire [`XLEN_R] calc_sltiu = {{31{1'b0}}, (i_rs1 < sext_iimm)};
wire [`XLEN_R] calc_xori = i_rs1 ^ sext_iimm;
wire [`XLEN_R] calc_ori  = i_rs1 | sext_iimm;
wire [`XLEN_R] calc_andi = i_rs1 & sext_iimm;
wire [`XLEN_R] calc_slli  = i_rs1 << shamt;
wire [`XLEN_R] calc_srli  = i_rs1 >> shamt;
wire [`XLEN_R] calc_srai  = $signed(i_rs1) >>> shamt;
wire [`XLEN_R] calc_add = i_rs1 + i_rs2;
wire [`XLEN_R] calc_sub = $signed(i_rs1) - $signed(i_rs2);
wire [`XLEN_R] calc_sll  = i_rs1 << i_rs2[4:0];
wire [`XLEN_R] calc_slt = {{31{1'b0}}, ($signed(i_rs1) < $signed(i_rs2))};
wire [`XLEN_R] calc_sltu = {{31{1'b0}}, (i_rs1 < i_rs2)};
wire [`XLEN_R] calc_xor = i_rs1 ^ i_rs2;
wire [`XLEN_R] calc_srl   = i_rs1 >> i_rs2[4:0];
wire [`XLEN_R] calc_sra   = $signed(i_rs1) >>> i_rs2[4:0];
wire [`XLEN_R] calc_or  = i_rs1 | i_rs2;
wire [`XLEN_R] calc_and = i_rs1 & i_rs2;

`ff_cg_norst(reg [`XLEN_R], result, i_execute)
always @*
  (* parallel_case *)
  case (1'b1)
    (i_lui):   result_d = calc_lui;
    (i_auipc): result_d = calc_auipc;
    (i_addi):  result_d = calc_addi;
    (i_slti):  result_d = calc_slti;
    (i_sltiu): result_d = calc_sltiu;
    (i_xori):  result_d = calc_xori;
    (i_ori):   result_d = calc_ori;
    (i_andi):  result_d = calc_andi;
    (i_slli):  result_d = calc_slli;
    (i_srli):  result_d = calc_srli;
    (i_srai):  result_d = calc_srai;
    (i_add):   result_d = calc_add;
    (i_sub):   result_d = calc_sub;
    (i_sll):   result_d = calc_sll;
    (i_slt):   result_d = calc_slt;
    (i_sltu):  result_d = calc_sltu;
    (i_xor):   result_d = calc_xor;
    (i_srl):   result_d = calc_srl ;
    (i_sra):   result_d = calc_sra ;
    (i_or):    result_d = calc_or;
    (i_and):   result_d = calc_and;
    default:   result_d = 32'd0;
  endcase
assign o_result = result_q;

// Fixed 1 cycle calculation.
`ff_nocg_rst(reg, writeback, 1'b0)
always @* writeback_d = i_execute && (i_lui
                                   || i_auipc
                                   || i_addi
                                   || i_slti
                                   || i_sltiu
                                   || i_xori
                                   || i_ori
                                   || i_andi
                                   || i_slli
                                   || i_srli
                                   || i_srai
                                   || i_add
                                   || i_sub
                                   || i_sll
                                   || i_slt
                                   || i_sltu
                                   || i_xor
                                   || i_srl
                                   || i_sra
                                   || i_or
                                   || i_and);
assign o_xwrite = writeback_q;
assign o_complete = writeback_q;

endmodule // }}} alu_m

module lsu_m ( // {{{ Load Store Unit
  input wire i_clk,
  input wire i_rstn,

  // Data AXI Write address channel signals.
  output wire [`AXI_ADDR_W-1:0] o_axi_awaddr,
  output wire [2:0]             o_axi_awprot,
  output wire                   o_axi_awvalid,
  input  wire                   i_axi_awready,

  // Data AXI Write data channel signals.
  output wire [`AXI_DATA_W-1:0] o_axi_wdata,
  output wire [3:0]             o_axi_wstrb,
  output wire                   o_axi_wvalid,
  input  wire                   i_axi_wready,

  // Data AXI Write response channel signals.
  input  wire [1:0]             i_axi_bresp,
  input  wire                   i_axi_bvalid,
  output wire                   o_axi_bready,

  // Data AXI Read address channel signals.
  output wire [`AXI_ADDR_W-1:0] o_axi_araddr,
  output wire [2:0]             o_axi_arprot,
  output wire                   o_axi_arvalid,
  input  wire                   i_axi_arready,

  // Data AXI Read data channel signals.
  input  wire [`AXI_DATA_W-1:0] i_axi_rdata,
  input  wire [1:0]             i_axi_rresp,
  input  wire                   i_axi_rvalid,
  output wire                   o_axi_rready,

  input wire i_lb,
  input wire i_lh,
  input wire i_lw,
  input wire i_lbu,
  input wire i_lhu,
  input wire i_sb,
  input wire i_sh,
  input wire i_sw,
  input wire i_fence,

  input wire [11:0] i_iimm, // 11:0
  input wire [11:0] i_simm, // 11:0
  input wire [3:0]  i_prec,
  input wire [3:0]  i_succ,

  // xrf
  input wire [`XLEN_R] i_rs1,
  input wire [`XLEN_R] i_rs2,

  input wire i_execute,
  output wire o_xwrite,
  output wire [`XLEN_R] o_loadval,

  output wire o_lsucomplete,
  output wire o_lsutrap
);

wire [31:0] sext_iimm = {{20{i_iimm[11]}}, i_iimm};
wire [31:0] sext_simm = {{20{i_simm[11]}}, i_simm};

wire any_load = i_lb
             || i_lh
             || i_lw
             || i_lbu
             || i_lhu;

wire load = i_execute && any_load;

wire any_store = i_sb
              || i_sh
              || i_sw;

wire store = i_execute && any_store;

assign o_axi_awprot = 3'b010; // Data, Non-secure, Unpriviliged.
assign o_axi_arprot = 3'b010; // Data, Non-secure, Unpriviliged.

wire axi_aw = (i_axi_awready && o_axi_awvalid);
wire axi_w  = (i_axi_wready  && o_axi_wvalid);
wire axi_b  = (o_axi_bready  && i_axi_bvalid);
wire axi_ar = (i_axi_arready && o_axi_arvalid);
wire axi_r  = (o_axi_rready  && i_axi_rvalid);

// Indicate ready as soon an execution begins.
// Could tie these high?
assign o_axi_bready = any_store;
assign o_axi_rready = any_load;

wire [31:0] load_addr = i_rs1 + sext_iimm;
wire [31:0] store_addr = i_rs1 + sext_simm;

// Don't need full width adders to determine misaligned.
// Addition of both evens is always even, both odds is always even.
wire load_addr0 = i_rs1[0] ^ sext_iimm[0]; // (load_addr[0] != 1'b0)
wire [1:0] load_addr10 = i_rs1[1:0] + sext_iimm[1:0];

wire store_addr0 = i_rs1[0] ^ sext_simm[0]; // (store_addr[0] != 1'b0)
wire [1:0] store_addr10 = i_rs1[1:0] + sext_simm[1:0];

wire misaligned_load = ((i_lh || i_lhu) && (load_addr0 != 1'b0))
                     || (i_lw && (load_addr10 != 2'b00));

wire misaligned_store = (i_sh && (store_addr0 != 1'b0))
                     || (i_sw && (store_addr10 != 2'b00));

// Misaligned lh/lhu/sh are not necessarily split over 2 words, but lw/sw are
// always split and require 2 steps.
wire load_dualstep = ((i_lh || i_lhu) && (load_addr10 == 2'b11))
                  || (i_lw && (load_addr10 != 2'b00));
wire store_dualstep = (i_sh && (store_addr10 == 2'b11))
                   || (i_sw && (store_addr10 != 2'b00));

// 3 state FSM for memory requests. (IDLE=0, STEP1=1, STEP2=2)
// IDLE -> STEP1
// STEP1 -> IDLE
// STEP1 -> STEP2
// STEP2 -> IDLE
`ff_nocg_rst(reg [1:0], reqstep, 2'b0)
always @*
  case (reqstep_q)
    2'd0: begin
      if (load || store) reqstep_d = 2'd1; // IDLE -> STEP1
      else               reqstep_d = 2'd0; // nomove
    end
    2'd1: begin
      if (axi_ar || axi_aw) begin // Only move on AXI taken.
        if (load_dualstep || store_dualstep) reqstep_d = 2'd2; // STEP1 -> STEP2
        else                                 reqstep_d = 2'd0; // STEP1 -> IDLE
      end else
        reqstep_d = 2'd1; // nomove
    end
    2'd2: begin
      if (axi_ar || axi_aw) begin // Only move on AXI taken.
        reqstep_d = 2'd0; // STEP2 -> IDLE
      end else
        reqstep_d = 2'd2; // nomove
    end
    default: reqstep_d = 2'd0; // Return to IDLE
  endcase

// Output from dedicated ff, rather than just (any_store && |reqstep_q)
`ff_nocg_rst(reg, awvalid, 1'b0)
always @*
  if      (any_store && reqstep_d != 2'd0) awvalid_d = 1'b1;
  else if (axi_aw)                         awvalid_d = 1'b0;
  else                                     awvalid_d = awvalid_q;
assign o_axi_awvalid = awvalid_q;

// Only support AXI4lite where W channel is essentially the same as AW.
// Otherwise need a FIFO to queue each channel separately.
assign o_axi_wvalid = awvalid_q;


wire update_aw = store || (axi_aw && (reqstep_q == 2'd1));

`ff_cg_norst(reg [31:0], awaddr, update_aw)
always @*
  if (store) awaddr_d = store_addr;
  else       awaddr_d = store_addr + 4;
assign o_axi_awaddr = {awaddr_q[31:2], 2'd0}; // AXI address always word-aligned.


wire [31:0] rs2_l8  = {i_rs2[23: 0],  8'd0};
wire [31:0] rs2_l16 = {i_rs2[15: 0], 16'd0};
wire [31:0] rs2_l24 = {i_rs2[ 7: 0], 24'd0};
wire [31:0] rs2_r8  = { 8'd0, i_rs2[31: 8]};
wire [31:0] rs2_r16 = {16'd0, i_rs2[31:16]};
wire [31:0] rs2_r24 = {24'd0, i_rs2[31:24]};

`ff_cg_norst(reg [31:0], wdata, update_aw)
always @*
  (* parallel_case *)
  case (1'b1)
    (i_sb && store_addr10 == 2'd1): wdata_d = rs2_l8;
    (i_sb && store_addr10 == 2'd2): wdata_d = rs2_l16;
    (i_sb && store_addr10 == 2'd3): wdata_d = rs2_l24;
    (i_sh && store_addr10 == 2'd1): wdata_d = rs2_l8;
    (i_sh && store_addr10 == 2'd2): wdata_d = rs2_l16;
    (i_sh && store_addr10 == 2'd3 && (reqstep_d == 2'd1)): wdata_d = rs2_l24;
    (i_sh && store_addr10 == 2'd3 && (reqstep_d == 2'd2)): wdata_d = rs2_r8;
    (i_sw && store_addr10 == 2'd1 && (reqstep_d == 2'd1)): wdata_d = rs2_l8;
    (i_sw && store_addr10 == 2'd1 && (reqstep_d == 2'd2)): wdata_d = rs2_r24;
    (i_sw && store_addr10 == 2'd2 && (reqstep_d == 2'd1)): wdata_d = rs2_l16;
    (i_sw && store_addr10 == 2'd2 && (reqstep_d == 2'd2)): wdata_d = rs2_r16;
    (i_sw && store_addr10 == 2'd3 && (reqstep_d == 2'd1)): wdata_d = rs2_l24;
    (i_sw && store_addr10 == 2'd3 && (reqstep_d == 2'd2)): wdata_d = rs2_r8;
    default:  wdata_d = i_rs2; // word aligned, store_addr10 == 2'd0
  endcase
assign o_axi_wdata = wdata_q;

`ff_cg_norst(reg [3:0], wstrb, update_aw)
always @*
  (* parallel_case *)
  case (1'b1)
    (i_sb && store_addr10 == 2'd0): wstrb_d = 4'b0001;
    (i_sb && store_addr10 == 2'd1): wstrb_d = 4'b0010;
    (i_sb && store_addr10 == 2'd2): wstrb_d = 4'b0100;
    (i_sb && store_addr10 == 2'd3): wstrb_d = 4'b1000;
    (i_sh && store_addr10 == 2'd0): wstrb_d = 4'b0011;
    (i_sh && store_addr10 == 2'd1): wstrb_d = 4'b0110;
    (i_sh && store_addr10 == 2'd2): wstrb_d = 4'b1100;
    (i_sh && store_addr10 == 2'd3 && (reqstep_d == 2'd1)): wstrb_d = 4'b1000;
    (i_sh && store_addr10 == 2'd3 && (reqstep_d == 2'd2)): wstrb_d = 4'b0001;
    (i_sw && store_addr10 == 2'd1 && (reqstep_d == 2'd1)): wstrb_d = 4'b1110;
    (i_sw && store_addr10 == 2'd1 && (reqstep_d == 2'd2)): wstrb_d = 4'b0001;
    (i_sw && store_addr10 == 2'd2 && (reqstep_d == 2'd1)): wstrb_d = 4'b1100;
    (i_sw && store_addr10 == 2'd2 && (reqstep_d == 2'd2)): wstrb_d = 4'b0011;
    (i_sw && store_addr10 == 2'd3 && (reqstep_d == 2'd1)): wstrb_d = 4'b1000;
    (i_sw && store_addr10 == 2'd3 && (reqstep_d == 2'd2)): wstrb_d = 4'b0111;
    default: wstrb_d = 4'b1111; // sw aligned
  endcase
assign o_axi_wstrb = wstrb_q;



wire update_ar = load || (axi_ar && (reqstep_q == 2'd1));

`ff_cg_norst(reg [31:0], araddr, update_ar)
always @*
  if (load) araddr_d = load_addr;
  else      araddr_d = load_addr + 4;
assign o_axi_araddr = {araddr_q[31:2], 2'd0}; // AXI address always word-aligned.


// Output from dedicated ff, rather than just (any_load && |reqstep_q)
`ff_nocg_rst(reg, arvalid, 1'b0)
always @*
  if      (any_load && reqstep_d != 2'd0) arvalid_d = 1'b1;
  else if (axi_ar)                        arvalid_d = 1'b0;
  else                                    arvalid_d = arvalid_q;
assign o_axi_arvalid = arvalid_q;


// 3 state FSM for memory replies. (IDLE=0, STEP1=1, STEP2=2)
// IDLE -> STEP1
// STEP1 -> IDLE
// STEP1 -> STEP2
// STEP2 -> IDLE
`ff_nocg_rst(reg [1:0], repstep, 2'b0)
always @*
  case (repstep_q)
    2'd0: begin
      if (axi_ar || axi_aw) repstep_d = 2'd1; // IDLE -> STEP1
      else                  repstep_d = 2'd0; // nomove
    end
    2'd1: begin
      if (axi_r || axi_b) begin // Only move on AXI taken.
        if (load_dualstep || store_dualstep) repstep_d = 2'd2; // STEP1 -> STEP2
        else                                 repstep_d = 2'd0; // STEP1 -> IDLE
      end else
        repstep_d = 2'd1; // nomove
    end
    2'd2: begin
      if (axi_r || axi_b) begin // Only move on AXI taken.
        repstep_d = 2'd0; // STEP2 -> IDLE
      end else
        repstep_d = 2'd2; // nomove
    end
    default: repstep_d = 2'd0; // Return to IDLE
  endcase

wire rep_finish = (repstep_d == 2'd0) && (repstep_q != 2'd0);


reg [7:0] load_byte;
always @*
  case (load_addr10)
    2'd1:    load_byte = i_axi_rdata[15:8];
    2'd2:    load_byte = i_axi_rdata[23:16];
    2'd3:    load_byte = i_axi_rdata[31:24];
    default: load_byte = i_axi_rdata[7:0];
  endcase

reg [15:0] load_half;
always @*
  case (load_addr10)
    2'd1:    load_half = i_axi_rdata[23:8];
    2'd2:    load_half = i_axi_rdata[31:16];
    2'd3:
      if (repstep_q == 2'd1)  load_half = {8'd0, i_axi_rdata[31:24]};
      else                    load_half = {i_axi_rdata[7:0], 8'd0};
    default: load_half = i_axi_rdata[15:0];
  endcase

reg [31:0] load_word;
always @*
  case (load_addr10)
    2'd1:
      if (repstep_q == 2'd1)  load_word = {8'd0, i_axi_rdata[31:8]};
      else                    load_word = {i_axi_rdata[7:0], 24'd0};
    2'd2:
      if (repstep_q == 2'd1)  load_word = {16'd0, i_axi_rdata[31:16]};
      else                    load_word = {i_axi_rdata[15:0], 16'd0};
    2'd3:
      if (repstep_q == 2'd1)  load_word = {24'd0, i_axi_rdata[31:24]};
      else                    load_word = {i_axi_rdata[23:0], 8'd0};
    default: load_word = i_axi_rdata[31:0];
  endcase

reg [31:0] loadresult;
always @*
  (* parallel_case *)
  case (1'b1)
    (i_lb):  loadresult = {{24{load_byte[7]}}, load_byte};
    (i_lbu): loadresult = {{24{1'b0}}, load_byte};
    (i_lh):  loadresult = {{16{load_half[15]}}, load_half};
    (i_lhu): loadresult = {{16{1'b0}}, load_half};
    default: loadresult = load_word; // i_lw
  endcase

// NOTE: This is a lot of logic hanging from input pads before flops, better
// hope i_axi_rdata has plenty timing slack!
`ff_cg_norst(reg [`XLEN_R], loadval, (load || axi_r))
always @*
  if (load) loadval_d = 32'd0;
  else      loadval_d = loadval_q | loadresult;
assign o_loadval = loadval_q;

`ff_nocg_rst(reg, xwrite, 1'b0)
always @* xwrite_d = any_load && rep_finish && !xwrite_q;
assign o_xwrite = xwrite_q;

`ff_nocg_rst(reg, complete, 1'b0)
always @* complete_d = rep_finish;
assign o_lsucomplete = complete_q || (i_fence && i_execute);

// NOTE: Misaligned accesses can cause 2 traps.
`ff_nocg_rst(reg, lsutrap, 1'b0)
always @* lsutrap_d = (axi_r && i_axi_rresp[1]) || (axi_b && i_axi_bresp[1]);
assign o_lsutrap = lsutrap_q;

endmodule // }}} lsu_m

module xrf_m ( // {{{ X-Register File
  input wire i_clk,
  input wire i_rstn,

  input wire        i_xread,
  input wire [4:0]  i_rs1i,
  input wire [4:0]  i_rs2i,
  output wire [`XLEN_R] o_rs1,
  output wire [`XLEN_R] o_rs2,

  input wire            i_xwrite_bra,
  input wire            i_xwrite_csr,
  input wire            i_xwrite_alu,
  input wire            i_xwrite_lsu,
  input wire [`XLEN_R]  i_rd_bra,
  input wire [`XLEN_R]  i_rd_csr,
  input wire [`XLEN_R]  i_rd_alu,
  input wire [`XLEN_R]  i_rd_lsu,
  input wire [4:0]      i_rdi
);

wire xwrite = (i_rdi != 0) && (i_xwrite_bra
                            || i_xwrite_csr
                            || i_xwrite_alu
                            || i_xwrite_lsu);

reg [`XLEN_R] rd;
always @*
  (* parallel_case *)
  case (1'b1)
    (i_xwrite_bra): rd = i_rd_bra;
    (i_xwrite_csr): rd = i_rd_csr;
    (i_xwrite_alu): rd = i_rd_alu;
    default:        rd = i_rd_lsu; // i_xwrite_lsu
  endcase

`ff_cg_norst(reg [`XLEN_R], xreg1,  (xwrite && (i_rdi == 5'd1 )))
`ff_cg_norst(reg [`XLEN_R], xreg2,  (xwrite && (i_rdi == 5'd2 )))
`ff_cg_norst(reg [`XLEN_R], xreg3,  (xwrite && (i_rdi == 5'd3 )))
`ff_cg_norst(reg [`XLEN_R], xreg4,  (xwrite && (i_rdi == 5'd4 )))
`ff_cg_norst(reg [`XLEN_R], xreg5,  (xwrite && (i_rdi == 5'd5 )))
`ff_cg_norst(reg [`XLEN_R], xreg6,  (xwrite && (i_rdi == 5'd6 )))
`ff_cg_norst(reg [`XLEN_R], xreg7,  (xwrite && (i_rdi == 5'd7 )))
`ff_cg_norst(reg [`XLEN_R], xreg8,  (xwrite && (i_rdi == 5'd8 )))
`ff_cg_norst(reg [`XLEN_R], xreg9,  (xwrite && (i_rdi == 5'd9 )))
`ff_cg_norst(reg [`XLEN_R], xreg10, (xwrite && (i_rdi == 5'd10)))
`ff_cg_norst(reg [`XLEN_R], xreg11, (xwrite && (i_rdi == 5'd11)))
`ff_cg_norst(reg [`XLEN_R], xreg12, (xwrite && (i_rdi == 5'd12)))
`ff_cg_norst(reg [`XLEN_R], xreg13, (xwrite && (i_rdi == 5'd13)))
`ff_cg_norst(reg [`XLEN_R], xreg14, (xwrite && (i_rdi == 5'd14)))
`ff_cg_norst(reg [`XLEN_R], xreg15, (xwrite && (i_rdi == 5'd15)))
`ff_cg_norst(reg [`XLEN_R], xreg16, (xwrite && (i_rdi == 5'd16)))
`ff_cg_norst(reg [`XLEN_R], xreg17, (xwrite && (i_rdi == 5'd17)))
`ff_cg_norst(reg [`XLEN_R], xreg18, (xwrite && (i_rdi == 5'd18)))
`ff_cg_norst(reg [`XLEN_R], xreg19, (xwrite && (i_rdi == 5'd19)))
`ff_cg_norst(reg [`XLEN_R], xreg20, (xwrite && (i_rdi == 5'd20)))
`ff_cg_norst(reg [`XLEN_R], xreg21, (xwrite && (i_rdi == 5'd21)))
`ff_cg_norst(reg [`XLEN_R], xreg22, (xwrite && (i_rdi == 5'd22)))
`ff_cg_norst(reg [`XLEN_R], xreg23, (xwrite && (i_rdi == 5'd23)))
`ff_cg_norst(reg [`XLEN_R], xreg24, (xwrite && (i_rdi == 5'd24)))
`ff_cg_norst(reg [`XLEN_R], xreg25, (xwrite && (i_rdi == 5'd25)))
`ff_cg_norst(reg [`XLEN_R], xreg26, (xwrite && (i_rdi == 5'd26)))
`ff_cg_norst(reg [`XLEN_R], xreg27, (xwrite && (i_rdi == 5'd27)))
`ff_cg_norst(reg [`XLEN_R], xreg28, (xwrite && (i_rdi == 5'd28)))
`ff_cg_norst(reg [`XLEN_R], xreg29, (xwrite && (i_rdi == 5'd29)))
`ff_cg_norst(reg [`XLEN_R], xreg30, (xwrite && (i_rdi == 5'd30)))
`ff_cg_norst(reg [`XLEN_R], xreg31, (xwrite && (i_rdi == 5'd31)))

always @* xreg1_d = rd;
always @* xreg2_d = rd;
always @* xreg3_d = rd;
always @* xreg4_d = rd;
always @* xreg5_d = rd;
always @* xreg6_d = rd;
always @* xreg7_d = rd;
always @* xreg8_d = rd;
always @* xreg9_d = rd;
always @* xreg10_d = rd;
always @* xreg11_d = rd;
always @* xreg12_d = rd;
always @* xreg13_d = rd;
always @* xreg14_d = rd;
always @* xreg15_d = rd;
always @* xreg16_d = rd;
always @* xreg17_d = rd;
always @* xreg18_d = rd;
always @* xreg19_d = rd;
always @* xreg20_d = rd;
always @* xreg21_d = rd;
always @* xreg22_d = rd;
always @* xreg23_d = rd;
always @* xreg24_d = rd;
always @* xreg25_d = rd;
always @* xreg26_d = rd;
always @* xreg27_d = rd;
always @* xreg28_d = rd;
always @* xreg29_d = rd;
always @* xreg30_d = rd;
always @* xreg31_d = rd;

wire [`XLEN_R] xreg [31:0];
assign xreg[0] = `XLEN'd0;
assign xreg[1] = xreg1_q;
assign xreg[2] = xreg2_q;
assign xreg[3] = xreg3_q;
assign xreg[4] = xreg4_q;
assign xreg[5] = xreg5_q;
assign xreg[6] = xreg6_q;
assign xreg[7] = xreg7_q;
assign xreg[8] = xreg8_q;
assign xreg[9] = xreg9_q;
assign xreg[10] = xreg10_q;
assign xreg[11] = xreg11_q;
assign xreg[12] = xreg12_q;
assign xreg[13] = xreg13_q;
assign xreg[14] = xreg14_q;
assign xreg[15] = xreg15_q;
assign xreg[16] = xreg16_q;
assign xreg[17] = xreg17_q;
assign xreg[18] = xreg18_q;
assign xreg[19] = xreg19_q;
assign xreg[20] = xreg20_q;
assign xreg[21] = xreg21_q;
assign xreg[22] = xreg22_q;
assign xreg[23] = xreg23_q;
assign xreg[24] = xreg24_q;
assign xreg[25] = xreg25_q;
assign xreg[26] = xreg26_q;
assign xreg[27] = xreg27_q;
assign xreg[28] = xreg28_q;
assign xreg[29] = xreg29_q;
assign xreg[30] = xreg30_q;
assign xreg[31] = xreg31_q;

`ff_cg_norst(reg [`XLEN_R], rs1, i_xread)
always @* rs1_d = xreg[i_rs1i];
assign o_rs1 = rs1_q;

`ff_cg_norst(reg [`XLEN_R], rs2, i_xread)
always @* rs2_d = xreg[i_rs2i];
assign o_rs2 = rs2_q;

endmodule // }}} xrf_m

module rsm_m ( // {{{
  input wire i_clk,
  input wire i_rstn,


  // Instruction AXI Read address channel signals.
  output wire [`AXI_ADDR_W-1:0] o_axi_ifu_araddr,
  output wire [2:0]             o_axi_ifu_arprot,
  output wire                   o_axi_ifu_arvalid,
  input  wire                   i_axi_ifu_arready,

  // Instruction AXI Read data channel signals.
  input  wire [`AXI_DATA_W-1:0] i_axi_ifu_rdata,
  input  wire [1:0]             i_axi_ifu_rresp,
  input  wire                   i_axi_ifu_rvalid,
  output wire                   o_axi_ifu_rready,


  // Data AXI Write address channel signals.
  output wire [`AXI_ADDR_W-1:0] o_axi_lsu_awaddr,
  output wire [2:0]             o_axi_lsu_awprot,
  output wire                   o_axi_lsu_awvalid,
  input  wire                   i_axi_lsu_awready,

  // Data AXI Write data channel signals.
  output wire [`AXI_DATA_W-1:0] o_axi_lsu_wdata,
  output wire [3:0]             o_axi_lsu_wstrb,
  output wire                   o_axi_lsu_wvalid,
  input  wire                   i_axi_lsu_wready,

  // Data AXI Write response channel signals.
  input  wire [1:0]             i_axi_lsu_bresp,
  input  wire                   i_axi_lsu_bvalid,
  output wire                   o_axi_lsu_bready,

  // Data AXI Read address channel signals.
  output wire [`AXI_ADDR_W-1:0] o_axi_lsu_araddr,
  output wire [2:0]             o_axi_lsu_arprot,
  output wire                   o_axi_lsu_arvalid,
  input  wire                   i_axi_lsu_arready,

  // Data AXI Read data channel signals.
  input  wire [`AXI_DATA_W-1:0] i_axi_lsu_rdata,
  input  wire [1:0]             i_axi_lsu_rresp,
  input  wire                   i_axi_lsu_rvalid,
  output wire                   o_axi_lsu_rready
);

  // {{{ wires

  wire fetch;
  wire [31:0] pc; // IADDR_W

  wire [31:0] ir; // Instruction Register, INSN_W
  wire ir_valid;

  wire insn_jal;
  wire insn_jalr;
  wire insn_beq;
  wire insn_bne;
  wire insn_blt;
  wire insn_bge;
  wire insn_bltu;
  wire insn_bgeu;
  wire insn_ecall;
  wire insn_ebreak;

  wire insn_csrrw;
  wire insn_csrrs;
  wire insn_csrrc;
  wire insn_csrrwi;
  wire insn_csrrsi;
  wire insn_csrrci;

  wire insn_lui;
  wire insn_auipc;
  wire insn_addi;
  wire insn_slti;
  wire insn_sltiu;
  wire insn_xori;
  wire insn_ori;
  wire insn_andi;
  wire insn_slli;
  wire insn_srli;
  wire insn_srai;
  wire insn_add;
  wire insn_sub;
  wire insn_sll;
  wire insn_slt;
  wire insn_sltu;
  wire insn_xor;
  wire insn_srl;
  wire insn_sra;
  wire insn_or;
  wire insn_and;

  wire insn_lb;
  wire insn_lh;
  wire insn_lw;
  wire insn_lbu;
  wire insn_lhu;
  wire insn_sb;
  wire insn_sh;
  wire insn_sw;
  wire insn_fence;
  wire insn_fencei;

  wire [4:0] rs1i;
  wire [4:0] rs2i;
  wire [`XLEN_R] rs1;
  wire [`XLEN_R] rs2;

  wire xwrite_bra;
  wire xwrite_csr;
  wire xwrite_alu;
  wire xwrite_lsu;
  wire [`XLEN_R] rd_bra;
  wire [`XLEN_R] rd_csr;
  wire [`XLEN_R] rd_alu;
  wire [`XLEN_R] rd_lsu;
  wire [4:0] rdi;

  wire ifucomplete;
  wire alucomplete;
  wire csrcomplete;
  wire lsucomplete;

  wire instret;
  wire execute;
  wire ifutrap;
  wire dectrap;
  wire lsutrap;
  wire csrtrap;

  wire [11:0] iimm; // 11:0
  wire [11:0] simm; // 20:1
  wire [12:0] bimm; // 12:1
  wire [31:0] uimm; // 31:12
  wire [20:0] jimm; // 20:1
  wire [4:0]  zimm; // 4:0

  wire [3:0] prec;
  wire [3:0] succ;

  // }}} wires

  ifu_m ifu_u ( // {{{
    .i_clk(i_clk),
    .i_rstn(i_rstn),

    .o_axi_araddr (o_axi_ifu_araddr),
    .o_axi_arprot (o_axi_ifu_arprot),
    .o_axi_arvalid(o_axi_ifu_arvalid),
    .i_axi_arready(i_axi_ifu_arready),

    .i_axi_rdata  (i_axi_ifu_rdata),
    .i_axi_rresp  (i_axi_ifu_rresp),
    .i_axi_rvalid (i_axi_ifu_rvalid),
    .o_axi_rready (o_axi_ifu_rready),

    .i_fencei(insn_fencei),
    .i_execute(execute),
    .o_ifucomplete(ifucomplete),
    .o_ifutrap(ifutrap),

    .i_fetch(fetch),
    .i_pc(pc),

    .o_ir(ir),
    .o_ir_valid(ir_valid)
  ); // }}} ifu_u

  dec_m dec_u ( // {{{
    .i_clk(i_clk),
    .i_rstn(i_rstn),

    .i_ir(ir),
    .i_ir_valid(ir_valid),

    .o_fencei(insn_fencei),

    .o_jal   (insn_jal),
    .o_jalr  (insn_jalr),
    .o_beq   (insn_beq),
    .o_bne   (insn_bne),
    .o_blt   (insn_blt),
    .o_bge   (insn_bge),
    .o_bltu  (insn_bltu),
    .o_bgeu  (insn_bgeu),
    .o_ecall (insn_ecall),
    .o_ebreak(insn_ebreak),

    .o_csrrw (insn_csrrw),
    .o_csrrs (insn_csrrs),
    .o_csrrc (insn_csrrc),
    .o_csrrwi(insn_csrrwi),
    .o_csrrsi(insn_csrrsi),
    .o_csrrci(insn_csrrci),

    .o_lui   (insn_lui),
    .o_auipc (insn_auipc),
    .o_addi  (insn_addi),
    .o_slti  (insn_slti),
    .o_sltiu (insn_sltiu),
    .o_xori  (insn_xori),
    .o_ori   (insn_ori),
    .o_andi  (insn_andi),
    .o_slli  (insn_slli),
    .o_srli  (insn_srli),
    .o_srai  (insn_srai),
    .o_add   (insn_add),
    .o_sub   (insn_sub),
    .o_sll   (insn_sll),
    .o_slt   (insn_slt),
    .o_sltu  (insn_sltu),
    .o_xor   (insn_xor),
    .o_srl   (insn_srl),
    .o_sra   (insn_sra),
    .o_or    (insn_or),
    .o_and   (insn_and),

    .o_lb    (insn_lb),
    .o_lh    (insn_lh),
    .o_lw    (insn_lw),
    .o_lbu   (insn_lbu),
    .o_lhu   (insn_lhu),
    .o_sb    (insn_sb),
    .o_sh    (insn_sh),
    .o_sw    (insn_sw),
    .o_fence (insn_fence),

    .o_iimm(iimm),
    .o_simm(simm),
    .o_bimm(bimm),
    .o_uimm(uimm),
    .o_jimm(jimm),
    .o_zimm(zimm),

    .o_prec(prec),
    .o_succ(succ),

    .o_rs1i(rs1i),
    .o_rs2i(rs2i),
    .o_rdi(rdi),

    .o_execute(execute),
    .o_dectrap(dectrap)
  ); // }}} dec_u

  bra_m bra_u ( // {{{
    .i_clk(i_clk),
    .i_rstn(i_rstn),

    .i_ifucomplete(ifucomplete),
    .i_csrcomplete(csrcomplete),
    .i_alucomplete(alucomplete),
    .i_lsucomplete(lsucomplete),

    .i_ifutrap(ifutrap),
    .i_dectrap(dectrap),
    .i_csrtrap(csrtrap),
    .i_lsutrap(lsutrap),

    .i_jal   (insn_jal),
    .i_jalr  (insn_jalr),
    .i_beq   (insn_beq),
    .i_bne   (insn_bne),
    .i_blt   (insn_blt),
    .i_bge   (insn_bge),
    .i_bltu  (insn_bltu),
    .i_bgeu  (insn_bgeu),
    .i_ecall (insn_ecall),
    .i_ebreak(insn_ebreak),

    .i_bimm(bimm),
    .i_iimm(iimm),
    .i_jimm(jimm),

    .i_rs1(rs1),
    .i_rs2(rs2),
    .o_xwrite(xwrite_bra),
    .o_linkpc(rd_bra),

    .o_instret(instret),

    .i_execute(execute),
    .o_fetch(fetch),
    .o_pc(pc)
  ); // }}} bra_u

  csr_m csr_u ( // {{{
    .i_clk(i_clk),
    .i_rstn(i_rstn),

    .i_csrrw (insn_csrrw),
    .i_csrrs (insn_csrrs),
    .i_csrrc (insn_csrrc),
    .i_csrrwi(insn_csrrwi),
    .i_csrrsi(insn_csrrsi),
    .i_csrrci(insn_csrrci),

    .i_iimm(iimm),
    .i_zimm(zimm),
    .i_rdi(rdi),

    .i_rs1(rs1),
    .o_xwrite(xwrite_csr),
    .o_csrval(rd_csr),

    .i_instret(instret),

    .i_execute(execute),
    .o_csrcomplete(csrcomplete),
    .o_csrtrap(csrtrap)
  ); // }}} csr_u

  alu_m alu_u ( // {{{
    .i_clk(i_clk),
    .i_rstn(i_rstn),

    .i_iimm  (iimm),
    .i_uimm  (uimm),

    .i_lui   (insn_lui),
    .i_auipc (insn_auipc),
    .i_addi  (insn_addi),
    .i_slti  (insn_slti),
    .i_sltiu (insn_sltiu),
    .i_xori  (insn_xori),
    .i_ori   (insn_ori),
    .i_andi  (insn_andi),
    .i_slli  (insn_slli),
    .i_srli  (insn_srli),
    .i_srai  (insn_srai),
    .i_add   (insn_add),
    .i_sub   (insn_sub),
    .i_sll   (insn_sll),
    .i_slt   (insn_slt),
    .i_sltu  (insn_sltu),
    .i_xor   (insn_xor),
    .i_srl   (insn_srl),
    .i_sra   (insn_sra),
    .i_or    (insn_or),
    .i_and   (insn_and),

    .i_pc(pc),

    .i_rs1(rs1),
    .i_rs2(rs2),

    .i_execute(execute),
    .o_complete(alucomplete),
    .o_xwrite(xwrite_alu),
    .o_result(rd_alu)
  ); // }}} alu_u

  lsu_m lsu_u ( // {{{
    .i_clk(i_clk),
    .i_rstn(i_rstn),


    .o_axi_awaddr (o_axi_lsu_awaddr),
    .o_axi_awprot (o_axi_lsu_awprot),
    .o_axi_awvalid(o_axi_lsu_awvalid),
    .i_axi_awready(i_axi_lsu_awready),

    .o_axi_wdata  (o_axi_lsu_wdata),
    .o_axi_wstrb  (o_axi_lsu_wstrb),
    .o_axi_wvalid (o_axi_lsu_wvalid),
    .i_axi_wready (i_axi_lsu_wready),

    .i_axi_bresp  (i_axi_lsu_bresp),
    .i_axi_bvalid (i_axi_lsu_bvalid),
    .o_axi_bready (o_axi_lsu_bready),


    .o_axi_araddr (o_axi_lsu_araddr),
    .o_axi_arprot (o_axi_lsu_arprot),
    .o_axi_arvalid(o_axi_lsu_arvalid),
    .i_axi_arready(i_axi_lsu_arready),

    .i_axi_rdata  (i_axi_lsu_rdata),
    .i_axi_rresp  (i_axi_lsu_rresp),
    .i_axi_rvalid (i_axi_lsu_rvalid),
    .o_axi_rready (o_axi_lsu_rready),


    .i_lb    (insn_lb),
    .i_lh    (insn_lh),
    .i_lw    (insn_lw),
    .i_lbu   (insn_lbu),
    .i_lhu   (insn_lhu),
    .i_sb    (insn_sb),
    .i_sh    (insn_sh),
    .i_sw    (insn_sw),
    .i_fence (insn_fence),

    .i_iimm(iimm),
    .i_simm(simm),
    .i_prec(prec),
    .i_succ(succ),

    .i_rs1(rs1),
    .i_rs2(rs2),

    .i_execute(execute),
    .o_xwrite(xwrite_lsu),
    .o_loadval(rd_lsu),

    .o_lsucomplete(lsucomplete),
    .o_lsutrap(lsutrap)
  ); // }}} lsu_u

  xrf_m xrf_u ( // {{{
    .i_clk(i_clk),
    .i_rstn(i_rstn),

    .i_xread(ir_valid),
    .i_rs1i(rs1i),
    .i_rs2i(rs2i),
    .o_rs1(rs1),
    .o_rs2(rs2),

    .i_xwrite_bra(xwrite_bra),
    .i_xwrite_csr(xwrite_csr),
    .i_xwrite_alu(xwrite_alu),
    .i_xwrite_lsu(xwrite_lsu),
    .i_rd_bra(rd_bra),
    .i_rd_csr(rd_csr),
    .i_rd_alu(rd_alu),
    .i_rd_lsu(rd_lsu),
    .i_rdi(rdi)
  ); // }}} xrf_u

endmodule // }}} rsm_m

