/** popcnt6_m.sv - Population count of up to 6 bits.
 * Can be used as part of a more generic popcnt module.
 */
module popcnt6 #(
  parameter ABSTRACT_MODEL = 0 // Set for faster simulation.
) (
  input  wire [5:0]  i_x,
  output wire [2:0]  o_count
);

integer i;
genvar j;

generate if (ABSTRACT_MODEL) begin : abstractModel
  reg [2:0] count;
  always @* begin
    count = 3'd0;
    for (i = 0; i < 6; i=i+1) if (i_x[i]) count = count + 1;
  end

  assign o_count = count;
end : abstractModel
else begin : realModel

  wire [1:0] ha_bits  [3];
  wire [2:0] ha_sum;
  wire [2:0] ha_carry;
  wire       ge2_sums;
  wire       ge2_carrys;
  wire       eq2_sums;
  wire       eq1_carrys;

  assign ha_bits[0] = {i_x[3], i_x[0]};
  assign ha_bits[1] = {i_x[4], i_x[1]};
  assign ha_bits[2] = {i_x[5], i_x[2]};

  for (j = 0; j < 3; j=j+1) begin : halfAdders
    assign ha_sum[j]   = ^ha_bits[j];
    assign ha_carry[j] = &ha_bits[j];
  end : halfAdders

  assign ge2_sums =
    (ha_sum[0] && ha_sum[1]) ||
    (ha_sum[1] && ha_sum[2]) ||
    (ha_sum[2] && ha_sum[0]);

  assign eq2_sums = !(&ha_sum) && ge2_sums;

  assign ge2_carrys =
    (ha_carry[0] && ha_carry[1]) ||
    (ha_carry[1] && ha_carry[2]) ||
    (ha_carry[2] && ha_carry[0]);

  assign eq1_carrys = |ha_carry && !ge2_carrys;

  assign o_count[0] = ^ha_sum;
  assign o_count[1] = &ha_carry || &ha_sum || (eq2_sums ^ eq1_carrys);
  assign o_count[2] = ge2_carrys || (|ha_carry && ge2_sums);

end : realModel endgenerate

endmodule

