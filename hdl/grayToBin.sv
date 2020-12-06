
module grayToBin #(
  parameter WIDTH = 8
) (
  input  wire [WIDTH-1:0]     i_gray,
  output wire [WIDTH-1:0]     o_bin
);

genvar i;

generate for (i = 0; i < WIDTH; i=i+1) begin
  assign o_bin[i] = ^(i_gray >> i);
end endgenerate

endmodule
