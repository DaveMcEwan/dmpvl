
// BAD: valid SV, but won't parse when pp keywords are ignored.
// Module declaration can be moved to a different file.
`ifdef FOO
module A #(
`else
module B #(
`endif

// GOOD: valid SV will parse when pp keywords are ignored.
// Same rule applies to all comma-separated lists.
`ifdef FOO
  parameter a = 1,
`else
  parameter a = 2,
`endif

// BAD: valid SV will parse when pp keywords are ignored.
// Last element does not have a comma.
`ifdef FOO
  parameter b = 1
`else
  parameter b = 2
`endif
) foo ();

// GOOD: valid SV will parse when pp keywords are ignored.
`ifdef FOO
assign aa = 123;
`else
assign aa = 456;
`endif

// BAD: valid SV, but won't parse when pp keywords are ignored.
assign ab =
`ifdef FOO
  123;
`else
  456;
`endif

endmodule
