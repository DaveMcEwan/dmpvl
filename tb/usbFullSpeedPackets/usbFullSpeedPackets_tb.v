/** Testbench for one way USB Full Speed packet send/receive.
 *
 * 1. usbFullSpeedPacketSender[host] (verif) --> usbFullSpeedPacketReceiver[device] (verif)
 * 2. usbFullSpeedPacketSender[host] (verif) --> usbPktRx (VGWM design)
 * 3. usbFullSpeedPacketSender[host] (verif) --> usbfsPktRx (design)
 * TODO: usbfsPktTx[dev] (design) --> usbFullSpeedPacketReceiver[device] (verif)
 */
module usbFullSpeedPackets_tb (
`ifdef VERILATOR // V_erilator testbench can only drive IO from C++.
  `error No Verilator testbench here!
  input wire i_rootClk,
`endif
);

`include "usbSpec.svh"

wire [3:0]            drvHost_o_pid;
wire [8*8-1:0]        drvHost_o_data;
wire [$clog2(8):0]    drvHost_o_data_nBytes;
wire                  host_o_ready;
wire                  host_i_valid;
wire                  host_o_eopDone;
wire                  host_o_dp;
wire                  host_o_dn;
wire                  host_o_inflight;

wire                  vdev_o_strobe_12MHz;
wire                  vdev_o_sop;
wire                  vdev_o_eop;
wire                  vdev_o_inflight;
wire [3:0]            vdev_o_pid;
wire [8*8-1:0]        vdev_o_lastData;
wire [$clog2(8):0]    vdev_o_lastData_nBytes;
wire [6:0]            vdev_o_lastAddr;
wire [3:0]            vdev_o_lastEndp;
wire                  vdev_o_pidOkay;
wire                  vdev_o_tokenOkay;
wire                  vdev_o_dataOkay;

wire                  VGWM_dev_o_bitStrobe;
wire                  VGWM_dev_o_pktBegin;
wire                  VGWM_dev_o_pktEnd;
wire [3:0]            VGWM_dev_o_pid;
wire [6:0]            VGWM_dev_o_addr;
wire [3:0]            VGWM_dev_o_endp;
wire [10:0]           VGWM_dev_o_frameNum;
wire                  VGWM_dev_o_dataPut;
wire [7:0]            VGWM_dev_o_data;
wire                  VGWM_dev_o_pktValid;

wire                  dev_o_strobe_12MHz;
wire                  dev_o_eop;
wire                  dev_o_inflight;
wire [3:0]            dev_o_pid;
wire [8*8-1:0]        dev_o_lastData;
wire [$clog2(8):0]    dev_o_lastData_nBytes;
wire [6:0]            dev_o_addr;
wire [3:0]            dev_o_endp;
wire                  dev_o_pidOkay;
wire                  dev_o_tokenOkay;
wire                  dev_o_dataOkay;


wire clk_12MHz;
wire clk_48MHz;
reg rst;

`ifndef VERILATOR // {{{ Non-V_erilator tb

initial begin
  $dumpfile("build/usbFullSpeedPackets_tb.iverilog.vcd");
  $dumpvars(0, usbFullSpeedPackets_tb);
end

drivePackets v_drivePackets_host ( // {{{
  .i_clk                    (clk_12MHz),
  .i_rst                    (rst),

  .i_ready                  (host_o_ready),
  .o_valid                  (host_i_valid),

  .o_pid                    (drvHost_o_pid),
  .o_data                   (drvHost_o_data),
  .o_data_nBytes            (drvHost_o_data_nBytes)
); // }}} v_drivePackets_host

`endif // }}} Non-V_erilator tb

generateClock u_clk_12MHz (
`ifdef VERILATOR // V_erilator must drive its own root clock
  .i_rootClk        (i_rootClk),
`endif
  .o_clk            (clk_12MHz),
  .i_periodHi       (8'd3),
  .i_periodLo       (8'd3),
  .i_jitterControl  (8'd0)
);

generateClock u_clk_48MHz (
`ifdef VERILATOR // V_erilator must drive its own root clock
  .i_rootClk        (i_rootClk),
`endif
  .o_clk            (clk_48MHz),
  .i_periodHi       (8'd0),
  .i_periodLo       (8'd0),
  .i_jitterControl  (8'd0)
);

`dff_nocg_norst(reg [31:0], nCycles, clk_12MHz)
initial nCycles_q = '0;
always @*
  nCycles_d = nCycles_q + 'd1;

always @*
  if (nCycles_q > 5)
    rst = 1'b0;
  else
    rst = 1'b1;

wire host_accepted = host_o_ready && host_i_valid;
`dff_nocg_srst(reg [31:0], nPkts, clk_12MHz, rst, '0)
always @*
  if (host_accepted)
    nPkts_d = nPkts_q + 1;
  else
    nPkts_d = nPkts_q;

// Finish sim after an upper limit on the number of clock cycles, or USB
// transactions sent.
always @*
  if ((nCycles_q > 10000) || (nPkts_q > 1000))
    $finish;

// Should not accept another packet while one is inflight.
`asrt(drvAccept, clk_12MHz, !rst, !(host_o_inflight && host_accepted))

usbFullSpeedPacketSender #( // {{{ v_usbFullSpeedPacketSender_host
  .AS_HOST_NOT_DEV  (1),
  .MAX_PKT          (8)  // TODO?: Other sizes {8, 16, 32, 64}
) v_usbFullSpeedPacketSender_host (
  .i_clk_12MHz              (clk_12MHz),
  .i_rst                    (rst),

  .o_ready                  (host_o_ready),
  .i_valid                  (host_i_valid),

  .o_eopDone                (host_o_eopDone),

  .i_pid                    (drvHost_o_pid),
  .i_data                   (drvHost_o_data),
  .i_data_nBytes            (drvHost_o_data_nBytes),

  .o_dp                     (host_o_dp),
  .o_dn                     (host_o_dn),
  .o_inflight               (host_o_inflight)
); // }}} v_usbFullSpeedPacketSender_host

// TODO: Assertions that outputs should match expected.
// TODO: Assertions that design/implementation should match.
usbFullSpeedPacketReceiver #( // {{{ v_usbFullSpeedPacketReceiver_dev
  .AS_HOST_NOT_DEV  (0),
  .MAX_PKT          (8)  // TODO: Other sizes {8, 16, 32, 64}
) v_usbFullSpeedPacketReceiver_dev (
  .i_clk_48MHz          (clk_48MHz),
  .i_rst                (rst),

  .i_dp                 (host_o_dp),
  .i_dn                 (host_o_dn),

  .o_strobe_12MHz       (vdev_o_strobe_12MHz),

  .o_sop                (vdev_o_sop),
  .o_eop                (vdev_o_eop),
  .o_inflight           (vdev_o_inflight),

  .o_pid                (vdev_o_pid),
  .o_lastData           (vdev_o_lastData),
  .o_lastData_nBytes    (vdev_o_lastData_nBytes),

  .o_lastAddr           (vdev_o_lastAddr),
  .o_lastEndp           (vdev_o_lastEndp),

  .o_pidOkay            (vdev_o_pidOkay),
  .o_tokenOkay          (vdev_o_tokenOkay),
  .o_dataOkay           (vdev_o_dataOkay)
); // }}} v_usbFullSpeedPacketReceiver_dev

usbPktRx usbPktRx_dev ( // {{{
  .i_clk_48MHz          (clk_48MHz),
  .i_rst                (rst),

  // USB data+ and data- lines.
  .i_dp                 (host_o_dp),
  .i_dn                 (host_o_dn),

  // Pulse on every bit transition to synchronise with usbPktTx.
  .o_bitStrobe          (VGWM_dev_o_bitStrobe),

  // Pulse on beginning and end of each packet.
  .o_pktBegin           (VGWM_dev_o_pktBegin),
  .o_pktEnd             (VGWM_dev_o_pktEnd),

  // Most recent packet decoded.
  .o_pid                (VGWM_dev_o_pid),
  .o_addr               (VGWM_dev_o_addr),
  .o_endp               (VGWM_dev_o_endp),
  .o_frameNum           (VGWM_dev_o_frameNum),

  .o_dataPut            (VGWM_dev_o_dataPut), // Pulse on valid data on o_data.
  .o_data               (VGWM_dev_o_data),

  // Most recent packet passes PID and CRC checks
  .o_pktValid           (VGWM_dev_o_pktValid)
); // }}} usbPktRx_dev

usbfsPktRx #( // {{{ v_usbfsPktRx_dev
  .MAX_PKT          (8)  // TODO: Other sizes {8, 16, 32, 64}
) v_usbfsPktRx_dev (
  .i_clk_48MHz          (clk_48MHz),
  .i_rst                (rst),

  .i_dp                 (host_o_dp),
  .i_dn                 (host_o_dn),

  .o_strobe_12MHz       (dev_o_strobe_12MHz),

  .o_eop                (dev_o_eop),
  .o_inflight           (dev_o_inflight),

  .o_pid                (dev_o_pid),
  .o_addr               (dev_o_addr),
  .o_endp               (dev_o_endp),

  // TODO: Read buffer interface
  .i_rdEn               (1'b0),
  .i_rdIdx              (3'b0),
  .o_rdByte             (),
  .o_rdNBytes           (),

  .o_pidOkay            (dev_o_pidOkay),
  .o_tokenOkay          (dev_o_tokenOkay),
  .o_dataOkay           (dev_o_dataOkay)
); // }}} v_usbfsPktRx_dev

endmodule

