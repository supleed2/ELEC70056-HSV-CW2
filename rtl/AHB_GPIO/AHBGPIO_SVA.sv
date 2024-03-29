//////////////////////////////////////////////////////////////////////////////////
//END USER LICENCE AGREEMENT                                                    //
//                                                                              //
//Copyright (c) 2012, ARM All rights reserved.                                  //
//                                                                              //
//THIS END USER LICENCE AGREEMENT (�LICENCE�) IS A LEGAL AGREEMENT BETWEEN      //
//YOU AND ARM LIMITED ("ARM") FOR THE USE OF THE SOFTWARE EXAMPLE ACCOMPANYING  //
//THIS LICENCE. ARM IS ONLY WILLING TO LICENSE THE SOFTWARE EXAMPLE TO YOU ON   //
//CONDITION THAT YOU ACCEPT ALL OF THE TERMS IN THIS LICENCE. BY INSTALLING OR  //
//OTHERWISE USING OR COPYING THE SOFTWARE EXAMPLE YOU INDICATE THAT YOU AGREE   //
//TO BE BOUND BY ALL OF THE TERMS OF THIS LICENCE. IF YOU DO NOT AGREE TO THE   //
//TERMS OF THIS LICENCE, ARM IS UNWILLING TO LICENSE THE SOFTWARE EXAMPLE TO    //
//YOU AND YOU MAY NOT INSTALL, USE OR COPY THE SOFTWARE EXAMPLE.                //
//                                                                              //
//ARM hereby grants to you, subject to the terms and conditions of this Licence,//
//a non-exclusive, worldwide, non-transferable, copyright licence only to       //
//redistribute and use in source and binary forms, with or without modification,//
//for academic purposes provided the following conditions are met:              //
//a) Redistributions of source code must retain the above copyright notice, this//
//list of conditions and the following disclaimer.                              //
//b) Redistributions in binary form must reproduce the above copyright notice,  //
//this list of conditions and the following disclaimer in the documentation     //
//and/or other materials provided with the distribution.                        //
//                                                                              //
//THIS SOFTWARE EXAMPLE IS PROVIDED BY THE COPYRIGHT HOLDER "AS IS" AND ARM     //
//EXPRESSLY DISCLAIMS ANY AND ALL WARRANTIES, EXPRESS OR IMPLIED, INCLUDING     //
//WITHOUT LIMITATION WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR //
//PURPOSE, WITH RESPECT TO THIS SOFTWARE EXAMPLE. IN NO EVENT SHALL ARM BE LIABLE/
//FOR ANY DIRECT, INDIRECT, INCIDENTAL, PUNITIVE, OR CONSEQUENTIAL DAMAGES OF ANY/
//KIND WHATSOEVER WITH RESPECT TO THE SOFTWARE EXAMPLE. ARM SHALL NOT BE LIABLE //
//FOR ANY CLAIMS, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, //
//TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE    //
//EXAMPLE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE EXAMPLE. FOR THE AVOIDANCE/
// OF DOUBT, NO PATENT LICENSES ARE BEING LICENSED UNDER THIS LICENSE AGREEMENT.//
//////////////////////////////////////////////////////////////////////////////////


module AHBGPIO_SVA
( input  wire        HCLK
, input  wire        HRESETn
, input  wire [31:0] HADDR
, input  wire [ 1:0] HTRANS
, input  wire [31:0] HWDATA
, input  wire        HWRITE
, input  wire        HSEL
, input  wire        HREADY
, input  wire [16:0] GPIOIN
, input  wire        PARITYSEL
, input  wire        INJECT_FAULT
	//Output
, output wire        HREADYOUT
, output wire [31:0] HRDATA
, output wire [16:0] GPIOOUT
, output wire        PARITYERR
);

  localparam [7:0] gpio_data_addr = 8'h00;
  localparam [7:0] gpio_dir_addr = 8'h04;

  reg [15:0] gpio_dataout;
  reg        gpio_parityout;
  reg [15:0] gpio_datain;
  reg        gpio_parityerr;
  reg [15:0] gpio_dir;
  reg [15:0] gpio_data_next;
  reg [31:0] last_HADDR;
  reg [ 1:0] last_HTRANS;
  reg        last_HWRITE;
  reg        last_HSEL;

  assign HREADYOUT = 1'b1;

// Set Registers from address phase
  always_ff @(posedge HCLK)
    if(HREADY) begin
      last_HADDR <= HADDR;
      last_HTRANS <= HTRANS;
      last_HWRITE <= HWRITE;
      last_HSEL <= HSEL;
    end

  // Update in/out switch
  always_ff @(posedge HCLK, negedge HRESETn)
    if(!HRESETn)
      gpio_dir <= 16'h0000;
    else if ((last_HADDR[7:0] == gpio_dir_addr) & last_HSEL & last_HWRITE & last_HTRANS[1])
      gpio_dir <= HWDATA[15:0];

  // Update output value
  always_ff @(posedge HCLK, negedge HRESETn)
    if(!HRESETn)
      {gpio_parityout, gpio_dataout} <= 17'd0;
    else if ((gpio_dir == 16'h0001) & (last_HADDR[7:0] == gpio_data_addr) & last_HSEL & last_HWRITE & last_HTRANS[1]) begin
      gpio_dataout <= HWDATA[15:0];
      gpio_parityout <= ^{HWDATA[15:0],PARITYSEL,INJECT_FAULT};
    end

  // Update input value
  always_ff @(posedge HCLK, negedge HRESETn)
    if(!HRESETn) begin
      gpio_datain <= 16'h0000;
      gpio_parityerr <= '0;
    end
    else if (gpio_dir == 16'h0000) begin
      gpio_datain <= GPIOIN[15:0];
      gpio_parityerr <= ^{GPIOIN,PARITYSEL,INJECT_FAULT};
    end
    else if (gpio_dir == 16'h0001)
      gpio_datain <= GPIOOUT;

  assign HRDATA[15:0] = gpio_datain;
  assign GPIOOUT = {gpio_parityout, gpio_dataout};
  assign PARITYERR = gpio_parityerr;

  //check behaviour

  // assert_parity: assert property
  // ( @(posedge HCLK) disable iff (!HRESETn)
  //   !PARITYERR
  // );

  assert_gpio_write: assert property
  ( @(posedge HCLK) disable iff (!HRESETn)
    ((HADDR[7:0] == gpio_data_addr)
      && HSEL
      && HWRITE
      && HTRANS[1]
      && HREADY) |-> ##1
      (gpio_dir == 16'h0001) |-> ##1
    (GPIOOUT[15:0] == $past(HWDATA[15:0], 1) && (!$past(INJECT_FAULT,1) -> (^GPIOOUT == $past(PARITYSEL, 1))))
  );
  assert_gpio_read: assert property
  ( @(posedge HCLK) disable iff (!HRESETn)
    ((gpio_dir == 16'h0000)
      && (HADDR[7:0] == gpio_data_addr)
      // && HSEL // HSEL not used in Read always_ff
      && !HWRITE
      && HTRANS[1]
      && HREADY) |-> ##1
     ((HRDATA[15:0]==$past(GPIOIN[15:0],1)) && HREADYOUT && (!$past(INJECT_FAULT,1) -> !PARITYERR))
  );

  assert_gpio_dir: assert property
  ( @(posedge HCLK) disable iff (!HRESETn)
    ((HADDR[7:0] == gpio_dir_addr)
      && HSEL
      && HWRITE
      && HTRANS[1]
      && HREADY) |-> ##1
    ((HWDATA[7:0] == 8'h00 || HWDATA[7:0] == 8'h01)) |-> ##1 (gpio_dir == $past(HWDATA[15:0], 1))
  );

  assume_initial_valid: assume property
  ( @(posedge HCLK)
    gpio_dir == 16'h0000
    || gpio_dir == 16'h0001
  );

  assume_gpio_in_valid_parity: assume property
  ( @(posedge HCLK)
      (^GPIOIN == PARITYSEL)
  );

endmodule
