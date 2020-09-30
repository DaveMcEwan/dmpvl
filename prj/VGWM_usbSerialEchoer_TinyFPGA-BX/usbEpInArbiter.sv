module usbEpInArbiter #(
  parameter N_EP_IN = 1
) (
  input  wire [N_EP_IN-1:0]      i_inEp_req,
  output wire [N_EP_IN-1:0]      o_inEp_grant, // onehot
  input  wire [N_EP_IN*8-1:0]    i_inEp_data,
  output wire [7:0]              o_inEp_arbData
);

// TODO: Replace with fxcs configured as find-first-set.
assign o_inEp_grant[0] = i_inEp_req[0];

genvar i;
generate for (i=1; i < N_EP_IN; i=i+1) begin
  assign o_inEp_grant[i] = i_inEp_req[i] && !o_inEp_grant[i-1]; // smaller
  //assign o_inEp_grant[i] = i_inEp_req[i] && !(|i_inEp_req[i-1:0]); // faster
end endgenerate

reg [7:0] dataSelected;
integer j;
always @* begin
  dataSelected = i_inEp_data[7:0];
  for (j=0; j < N_EP_IN; j=j+1)
    if (o_inEp_grant[j])
      dataSelected = i_inEp_data[j*8 +: 8];
end

assign o_inEp_arbData = dataSelected;

endmodule
