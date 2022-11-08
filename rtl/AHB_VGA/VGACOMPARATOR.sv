module VGACOMPARATOR
( input  logic [31:0] HRDATA1
, input  logic        HREADYOUT1
, input  logic        HSYNC1
, input  logic        VSYNC1
, input  logic [ 7:0] RGB1
, input  logic [31:0] HRDATA2
, input  logic        HREADYOUT2
, input  logic        HSYNC2
, input  logic        VSYNC2
, input  logic [ 7:0] RGB2
, output logic        MISMATCH
);

  assign MISMATCH =
    !( HRDATA1 == HRDATA2
    && HREADYOUT1 == HREADYOUT2
    && HSYNC1 == HSYNC2
    && VSYNC1 == VSYNC2
    && RGB1 == RGB2
    )

endmodule