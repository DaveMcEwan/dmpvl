/* NOTE: Design perspective ->
  No example of interface with logic.
  No example of generic interface.
*/
package p;
  interface ifc_foo (
    input logic clk
  );
    logic a, b, c, d;
    modport upstream (
      input a, b,
      output c, d
    );
    modport downstream (
      output a, b,
      input c, d
    );
  endinterface

  typedef struct packed {
    logic c, d;
  } st_bar_us;

  typedef struct packed {
    logic a, b;
  } st_bar_ds;
endpackage


module top;
  logic clk1, clk2;
  p::ifc_foo.downstream uin_foo(clk1);
  p::st_bar_us bar_N2M;
  p::st_bar_ds bar_M2N;

  cpu M (
    .foo    (uin_foo),
    .i_bar  (bar_N2M),
    .o_bar  (bar_M2N),
    .clk    (clk2)
  );
endmodule


/* Cannot compile or synth at this level
IEEE1800-2017 Clause 23.3.3.4:
An interface port instance shall always be
connected to an interface instance or a higher
level interface port.
An interface port cannot be left unconnected.
*/
module cpu (
  p::ifc_foo.downstream foo,
  input  p::st_bar_ds   i_bar,
  output p::st_bar_us   o_bar,
  input                 clk
);

  assign foo.a = 1'b0; // Okay.

  // Multi-drive.
  // Naming convention doesn't help.
  assign foo.c = 1'b0; // Woops!

  // Should logic use foo.clk or clk?

  assign o_bar.c; // Okay.

  // Non-member.
  // Caught by compiler.
  assign o_bar.a; // Woops!

  // Multi-drive.
  // Highlighted by naming convention.
  assign i_bar.a; // Maybe woops?

endmodule

