module forbidSeqBlock ();
  logic clk, rst, clkgate;
  integer data_d, data_q;
  integer ctrl_d, ctrl_q;
  integer ping1_q, pong1_q;
  integer ping2_q, pong2_q;
  integer red_q, blue_q, green_q;

  // Non-reset DFF, e.g. data-path.
  always_ff @(posedge clk)
    data_q <= data_d;

  // Reset DFF, e.g. control-path.
  always_ff @(posedge clk)
    if (rst)
      ctrl_q <= '0;
    else if (clkgate)
      ctrl_q <= ctrl_d;
    else
      ctrl_q <= ctrl_q;

  // always_ff keyword prevents multi-driving of LHS.
  always_ff @(posedge clk)
    if (rst)
      foo_q <= '0;
    else if (clkgate)
      ctrl_q <= foo_d; // Woops!
    else
      foo_q <= foo_q;

  // Enforced exclusive updates.
  always_ff @(posedge clk)
    if (a)
      ping1_q <= data_q;
    else
      pong1_q <= data_q;

  // Enforced exclusive updates, with synchronous reset and clockgate.
  always_ff @(posedge clk)
    if (rst)
      {ping2_q, pong2_q} <= '0;
    else if (clkgate)
      if (a)
        ping2_q <= data_q;
      else
        pong2_q <= data_q;
  //else // Optional explicit `else` clause.
  //  {ping2_q, pong2_q} <= {ping2_q, pong2_q};

  // Enforced exclusivity of address decode.
  always_ff @(posedge clk)
    if (write)
      case (addr)
        123: red_q   <= data_q;
        456: blue_q  <= data_q;
        789: green_q <= data_q;
      endcase

endmodule
