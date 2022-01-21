module top #(bit FOO = 1) ();
  generate if (FOO)
    logic a;                // top.genblk1.a
  else
    logic b;                // top.genblk1.b
  endgenerate

  generate if (FOO) begin: la_Foo
    logic c;                // top.la_Foo.c
  end else begin: la_NotFoo
    logic d;                // top.la_NotFoo.d
  end endgenerate
endmodule
