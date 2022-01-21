package p;
  localparam int unsigned P_AW = 20;
  localparam bit [P_AW-1:0] A_ADDR = 'h123;
  localparam int            B_ADDR = 'h123;
  localparam int unsigned   C_ADDR = 'h123;
  localparam bit [31:0]     D_ADDR = 'h123;
endpackage

module example #(
  int unsigned P_AW = p::P_AW,
  // These should be overridden if P_AW is
  // overridden, otherwise width mis-match.
  bit [P_AW-1:0] A_ADDR0 = p::A_ADDR,
  // Or high bits can be dropped.
  bit [P_AW-1:0] A_ADDR1 = p::A_ADDR[P_AW-1:0],

  int unsigned M_AW = 12,
  // FOO should be overridden if M_AW is
  // overridden, otherwise width mis-match.
  bit [M_AW-1:0] FOO = 12'h004,
  // Unsized BAR is good for any value of M_AW.
  bit [M_AW-1:0] BAR = 'h004,

  // Let's not have to override addresses when we
  // change width, but still need to truncate later.
  int          B_ADDR = p::B_ADDR,
  int unsigned C_ADDR = p::C_ADDR,

  // Let's get warnings if ADDR doesn't fit.
  bit [M_AW-1:0] D_ADDR0 = (M_AW)'(p::B_ADDR),
  bit [M_AW-1:0] D_ADDR1 = (M_AW)'(p::C_ADDR),
  bit [M_AW-1:0] D_ADDR2 = (M_AW)'(p::D_ADDR)
) ();
endmodule
