module usbEpOutArbiter #(
  parameter N_EP_OUT = 1
) (
  input  wire [N_EP_OUT-1:0] i_outEp_req,
  output wire [N_EP_OUT-1:0] o_outEp_grant
);

assign o_outEp_grant[0] = i_outEp_req[0];

genvar i;
generate for (i=1; i < N_EP_OUT; i=i+1) begin
  assign o_outEp_grant[i] = i_outEp_req[i] && !o_outEp_grant[i-1]; // smaller
  //assign o_outEp_grant[i] = i_outEp_req[i] && !(|i_outEp_req[i-1:0]); // faster
end endgenerate

endmodule
