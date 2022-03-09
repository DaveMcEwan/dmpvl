/* Comma-Leading Style
<https://gist.github.com/isaacs/357981>
<https://github.com/tibbe/haskell-style-guide/blob/master/haskell-style.md#list-declarations>
*/

/* Module declaration without parameter ports.
*/
module Mod_A
( input  var logic i_abc // comment
, inout  var logic b_def /* comment */
, output var logic o_ghi
);
endmodule

/* Module declaration with parameter ports.
*/
module Mod_B
#(int FOO = 1 // comment
, bit BAR = 2 /* comment */
, bit [31:0] BAZ = 2
, parameter int BUZZ = 4
)
( input  var logic i_abc // comment
, inout  var logic b_def /* comment */
, output var logic o_ghi
);

/* Each item on its own line.
- Short lines.
- Every list indented to same level.
- Single-line LHS can be any length without indent issue.
*/
assign {foo, bar} =
  { i_abc
  , 12'h345
  , b_def     // comment
  , 16'h3456  /* comment */
  };

/* First item on same line.
*/
assign lessnice_A = { i_abc // No indent alignment issue.
                    , 12'h345
                    , b_def
                    , 16'h3456
                    };
assign lessnice_B_ =  { i_abc // Extra space after `=` to align with indent.
                      , 12'h345
                      , b_def
                      , 16'h3456
                      };

/* Everything fits on one line.
- No space after opening parenthesis/bracket/brace.
*/
assign singleline1D = {i_abc, 12'h345, b_def, 16'h3456};
assign singleline2D = {{foo, bar}, {foo, bar}, {foo, bar}};

/* Multi-dimensional concatenation with innermost array on one line.
*/
assign matrix2D_A =
  { {elem21, elem20}
  , {elem11, elem10} // comment
  , {elem01, elem00} /* comment */
  };
assign matrix3D_A =
  { { {elem211, elem210}
    , {elem201, elem200}
    }
  , { {elem111, elem110} // comment
    , {elem101, elem100} /* comment */
    }
  , { {elem011, elem010}
    , {elem001, elem000}
    }
  };

/* Multi-dimensional concatenation with innermost array on multiple lines.
*/ 
assign matrix2D_B =
  { { elem21
    , elem20
    }
  , { elem11 // comment
    , elem10 /* comment */
    }
  , { elem01
    , elem00
    }
  };
assign matrix3D_B =
  { { { elem211
      , elem210
      }
    , { elem201 // comment
      , elem200 /* comment */
      }
    }
  , { { elem110
      , elem110
      }
    , { elem100
      , elem100
      }
    }
  , { { elem010
      , elem010
      }
    , { elem000
      , elem000
      }
    }
  };

/* Module instance without parameter ports.
*/
Mod_A u_Mod_A0
( .i_abc(foo) // comment
, .b_def({bar, bar}) /* comment */
, .o_ghi
);

/* Module instance with parameter ports.
*/
Mod_B
#(.FOO(1) // comment
, .BAR(2) /* comment */
, .BUZZ(2)
) u_Mod_B
( .i_abc(foo) // comment
, .b_def({bar, bar}) /* comment */
, .o_ghi
);

endmodule
