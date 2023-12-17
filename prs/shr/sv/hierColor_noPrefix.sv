module A
  ( input  var logic        red
  , input  var logic [1:0]  blue
  , output var logic        green
  , output var logic        pink
  , output var logic [1:0]  black
  );

logic orange;

B u_B
  ( .red
  , .blue   (blue[0])
  , .green
  , .black  (black[0])
  , .orange
  );

C u_C
  ( .red
  , .blue   (blue[1])
  , .pink
  , .black  (black[1])
  , .orange
  );

endmodule
