package p;
  localparam int unsigned AW = 12;

  function bit [AW-1:0] foo ();
    return 123;
  endfunction
endpackage

module example ();
  localparam int unsigned AW = 20;
  localparam bit [AW-1:0] FOO = p::foo(); // Mis-matched width.
endmodule
