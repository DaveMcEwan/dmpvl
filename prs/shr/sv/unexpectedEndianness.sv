module bad #(
  int unsigned NUM_FLAGS = 5
) (
  output logic [NUM_FLAGS-1:0] o_flags // May be [-1:0].
);
  always_comb o_flags = 'd1;
endmodule

module good #(
  bit INCLUDE_FLAGS = 1,
  int unsigned NUM_FLAGS = 5
) (
  output logic [NUM_FLAGS-1:0] o_flags
);
  generate if (INCLUDE_FLAGS) begin
    always_comb o_flags = 'd1;
  end else begin
    always_comb o_flags = '0;
  end endgenerate
endmodule

module top ();
  // o_flags is 5b. Okay.
  bad #(.NUM_FLAGS(5)) okay5 (.o_flags());

  // o_flags is 1b. Okay.
  bad #(.NUM_FLAGS(1)) okay1 (.o_flags());

  // o_flags is 2b, little-endian. Woops!
  bad #(.NUM_FLAGS(0)) bad0  (.o_flags());

  // o_flags is default width (5b), but tied to zero. Okay.
  good #(.INCLUDE_FLAGS(0)) good0 (.o_flags());
endmodule
