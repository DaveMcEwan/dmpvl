/*
This is the endpoint to uart translator.
IN and OUT are set with respect to the HOST.
The HOST runs all endpoint interactions.


OUT (or into this device)

The USB innards signal that a packet has arrived by raising i_outEp_dataAvail.
The data multiplexor has to be switched, so the interface is requested.

With the interface granted, the data is free to get (take).
Every cycle that the o_outEp_dataGet signal is high, the input address is
advanced.
Inside the USB innards, when the read address pointer equals the address of the
write pointer (all the data is retreived) the i_outEp_dataAvail flag is lowered
and we withdraw our request for the interface and go back to idle.

Interestingly, if you stop taking data... you lose your buffer.  So don't.


IN (or out of this device back to the host)

The IN EP works by providing a buffer and waiting for the local logic to fill
it, or to say that it's done.
When this happens the interface switches to a new state where it waits for a
token from the host.
When it get the token, it sends the data.
When that is acknoledged, the buffer is released and returned ready to be
filled again.

i_inEp_dataFree signals that there's a buffer waiting.
And that signal goes low when the buffer is full and not available.

In the case where a buffer is not full - just sitting around with some data in
it, a decision has to be made at some point just to send.
This is handled by a timeout mechanism, which asserts o_inEp_dataDone and lets
the buffer be sent.

In the case where the buffer fills to the top, i_inEp_dataFree goes low by
itself.
*/

`include "dff.svh"

module usbEpBridge (
  input  wire         i_clk,
  input  wire         i_rst,

  output wire         o_outEp_req,        // Request use of OUT endpoint.
  input  wire         i_outEp_grant,      // Grant matching o_outEp_req.
  input  wire         i_outEp_dataAvail,  // Data is available to get from host.
                                          // Remains high until empty.
  input  wire         i_outEp_setup,      // unused. Setup packet sent.
  output wire         o_outEp_dataGet,    // Take a byte of data from usbPeOut.
  input  wire [7:0]   i_outEp_data,       // Data from the host, via usbPeOut.
  input  wire         i_outEp_acked,      // unused. Outgoing data was acked.

  output wire         o_inEp_req,         // request the data interface for the in endpoint
  input  wire         i_inEp_grant,       // data interface granted
  input  wire         i_inEp_dataFree,    // end point is ready for data - (specifically there is a buffer and it has space)
                                          // after going low it takes a while to get another back, but it does this automatically
  output wire         o_inEp_dataPut,     // forces end point to read our data
  output wire [7:0]   o_inEp_data,        // data back to the host
  output wire         o_inEp_dataDone,    // signalling that we're done sending data
  output wire         o_inEp_stall,       // an output enabling the device to stop outputs (not used)
  input  wire         i_inEp_acked,       // indicating that the outgoing data was acked

  input  wire [7:0]   i_uartIn_data,
  input  wire         i_uartIn_valid,
  output wire         o_uartIn_ready,

  output wire [7:0]   o_uartOut_data,  // To consumer.
  output wire         o_uartOut_valid, // Tell consumer data is waiting.
  input  wire         i_uartOut_ready  // Consumer is ready to take a byte from host.
);

// A request to use the OUT endpoint has been granted by usbPeOut.
wire outEp_reqGranted;
assign outEp_reqGranted = o_outEp_req && i_outEp_grant;

// {{{ Host-to-consumer buffer
wire fifoOut_full;
wire fifoOut_empty;
fifo #(
  .WIDTH          (8),
  .DEPTH          (8),
  .FLOPS_NOT_MEM  (0)
) u_fifoOut (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (1'b1),

  .i_flush    (1'b0), // unused
  .i_push     (i_outEp_dataAvail && o_outEp_dataGet),
  .i_pop      (i_uartOut_ready && o_uartOut_valid),

  .i_data     (i_outEp_data),
  .o_data     (o_uartOut_data),

  .o_empty    (fifoOut_empty),
  .o_full     (fifoOut_full),

  .o_pushed   (),
  .o_popped   (),

  .o_wrptr    (),
  .o_rdptr    (),

  .o_valid    (),
  .o_nEntries (),

  .o_entries  ()
);
// }}} Host-to-consumer buffer

`dff_nocg_srst(reg, outEp_dataGet, i_clk, i_rst, 1'b0)
`dff_nocg_srst(reg, outEp_req, i_clk, i_rst, 1'b0)

always @*
  if (!fifoOut_full && outEp_reqGranted)
    outEp_dataGet_d = 1'b1;
  else if (fifoOut_full || !i_outEp_dataAvail)
    outEp_dataGet_d = 1'b0;
  else
    outEp_dataGet_d = outEp_dataGet_q;

assign o_outEp_dataGet = outEp_dataGet_q;

always @*
  if (fifoOut_empty && outEp_reqGranted)
    outEp_req_d = 1'b1;
  else if (!fifoOut_empty && !i_uartOut_ready)
    outEp_req_d = 1'b0;
  else
    outEp_req_d = outEp_req_q;

assign o_uartOut_valid = !fifoOut_empty;

assign o_outEp_req = outEp_req_q || i_outEp_dataAvail;

assign o_inEp_stall = 1'b0;


wire inGranted;
wire inTimeoutExpired;
wire inAquireReq;
wire inReleaseReq;

`dff_nocg_srst(reg, inEp_req, i_clk, i_rst, 1'b0)
`dff_nocg_srst(reg, inEp_dataDone, i_clk, i_rst, 1'b0)

// {{{ inFsm
localparam IN_IDLE      = 0;
localparam IN_WAITDATA  = 1;
localparam IN_CYCLEDATA = 2;
localparam IN_WAITEP    = 3;
`dff_nocg_srst(reg [1:0], inFsm, i_clk, i_rst, IN_IDLE)
always @*
  case (inFsm_q)
    IN_IDLE:
      inFsm_d = (inGranted && i_inEp_dataFree) ? IN_CYCLEDATA : inFsm_q;

    IN_CYCLEDATA:
      if (i_uartIn_valid)
        inFsm_d = i_inEp_dataFree ? inFsm_q : IN_IDLE;
      else
        inFsm_d = IN_WAITDATA;

    IN_WAITDATA:
      if (i_uartIn_valid)
        inFsm_d = IN_CYCLEDATA;
      else if (inTimeoutExpired)
        inFsm_d = IN_WAITEP;
      else
        inFsm_d = inFsm_q;

    IN_WAITEP:
      inFsm_d = IN_IDLE;

    default:
      inFsm_d = IN_IDLE;
  endcase
// }}} inFsm

assign inGranted = i_inEp_grant && i_uartIn_valid;

// If we have a half filled buffer, send it after a while by using a timer
// 4 bits of counter, we'll just count up until bit 3 is high...
// 8 clock cycles seems more than enough to wait to send the packet.
localparam TIMEOUT_MSB = 3;
`dff_nocg_norst(reg [TIMEOUT_MSB:0], inTimeout, i_clk)
always @*
  if ((inFsm_q == IN_CYCLEDATA) && !i_uartIn_valid)
    // No valid byte.
    // Pause for a short time to see if any more bytes are forthcoming.
    inTimeout_d = '0;
  // TODO: Is !inTimeoutExpired required? Uses 6 LUTs.
  else if ((inFsm_q == IN_WAITDATA) && !inTimeoutExpired)
    inTimeout_d = inTimeout_q + 4'd1;  // NOTE: 4=TIMEOUT_MSB+1
  else
    inTimeout_d = inTimeout_q;

assign inTimeoutExpired = inTimeout_q[TIMEOUT_MSB];

assign inAquireReq =
  (inFsm_q == IN_IDLE) &&
   inGranted &&
   i_inEp_dataFree;

assign inReleaseReq =
  ((inFsm_q == IN_CYCLEDATA) &&
   i_uartIn_valid &&
   !i_inEp_dataFree) ||
  (inFsm_q == IN_WAITEP);

always @*
  if (inAquireReq)
    inEp_req_d = 1'b1;
  else if (inReleaseReq)
    inEp_req_d = 1'b0;
  else
    inEp_req_d = inEp_req_q;

always @*
  if ((inFsm_q == IN_IDLE) || (inFsm_q == IN_WAITEP))
    inEp_dataDone_d = 1'b0;
  else if ((inFsm_q == IN_WAITDATA) && !i_uartIn_valid && inTimeoutExpired)
    inEp_dataDone_d = 1'b1;
  else
    inEp_dataDone_d = inEp_dataDone_q;

// i_uartIn_valid and a buffer being ready is the request for the bus.
// It is granted automatically if available, and flopped by the FSM.
// Once requested, i_uartIn_valid may change as data is available.
// When requested, connect the end point registers to the outgoing ports
assign o_inEp_req =
  (i_uartIn_valid && i_inEp_dataFree) ||
  inEp_req_q;

assign o_inEp_dataPut =
  (inFsm_q == IN_CYCLEDATA) &&
  i_uartIn_valid &&
  i_inEp_dataFree;

assign o_inEp_dataDone = inEp_dataDone_q;

assign o_inEp_data = i_uartIn_data;

assign o_uartIn_ready =
  (inFsm_q == IN_CYCLEDATA) &&
  i_inEp_dataFree;

endmodule
