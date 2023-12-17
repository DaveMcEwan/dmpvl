module A
  ( input  var logic        i_red
  , input  var logic [1:0]  i_blue
  , output var logic        o_green
  , output var logic        o_pink
  , output var logic [1:0]  o_black
  );

  logic orange;

  B u_B
    ( .i_red
    , .i_blue   (i_blue[0])
    , .o_green
    , .o_black  (o_black[0])
    , .i_orange (orange)
    );

  C u_C
    ( .i_red
    , .i_blue   (i_blue[1])
    , .o_pink
    , .o_black  (o_black[1])
    , .o_orange (orange)
    );

endmodule
