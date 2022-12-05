module ahb_gpio_checker
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
, input wire        HREADYOUT
, input wire [31:0] HRDATA
, input wire [16:0] GPIOOUT
, input wire        PARITYERR
);

  logic             gpio_cmd =  HSEL && HREADY && HTRANS[1];
  logic             gpio_dir;
  localparam [7:0]  gpio_data_addr = 8'h00;
  localparam [7:0]  gpio_dir_addr = 8'h04;

// defined properties

  property gpio_write;
    @(posedge HCLK) disable iff (!HRESETn)
    (HADDR[7:0] == gpio_data_addr) && gpio_cmd
    ##1
    (gpio_dir=='1)
    ##1
    (GPIOOUT[15:0] == $past(HWDATA,1));
  endproperty

  property gpio_read;
    @(posedge HCLK) disable iff (!HRESETn)
    (HADDR[7:0] == gpio_data_addr) && gpio_cmd
    && (gpio_dir=='0)
    ##1
    ((HRDATA[15:0]==$past(GPIOIN[15:0],1)) && HREADYOUT);
  endproperty

  always_ff @(posedge HCLK)
  begin
    if(!HRESETn)
    begin
      gpio_dir            <= '0;
    end
    else
    begin
      if($past((gpio_cmd && (HADDR == gpio_dir_addr)),1))
      begin
        gpio_dir          <= HWDATA;
      end
    end
  end

// check behaviour
  assert_parity: assert property
  ( @(posedge HCLK) disable iff (!HRESETn)
    !PARITYERR
  );

  assert_gpio_write: assert property (gpio_write);
  assert_gpio_read:  assert property (gpio_read);

endmodule