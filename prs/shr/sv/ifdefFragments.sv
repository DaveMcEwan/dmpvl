
// BAD: valid SV, but won't parse when pp directives are ignored.
// Module declaration can be moved to a different file.
`ifdef FOO1
module ifdefFragmentsA
`else
module ifdefFragmentsB
`endif

// BAD: valid SV will parse when pp directives are ignored.
`ifdef FOO2
  #(parameter int X = 1
`else
  #(parameter int X = 2
`endif

// GOOD: valid SV will parse when pp directives are ignored.
// Same rule applies to all comma-separated lists.
`ifdef FOO3
  , parameter int Y = 1
`else
  , parameter int Y = 2
`endif

  ) ();

// GOOD: valid SV will parse when pp directives are ignored.
`ifdef FOO4
assign aa = 123;
`else
assign aa = 456;
`endif

// BAD: valid SV, but won't parse when pp directives are ignored.
assign ab =
`ifdef FOO5
  123;
`else
  456;
`endif

endmodule
