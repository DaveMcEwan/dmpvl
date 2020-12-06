
module binToGray #(
  parameter WIDTH = 8
) (
  input  wire [WIDTH-1:0]     i_bin,
  output wire [WIDTH-1:0]     o_gray
);

assign o_gray = (i_bin >> 1) ^ i_bin;

endmodule
