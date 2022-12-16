//stub
interface ahb_gpio_if;

  typedef enum bit[1:0] {
    IDLE = 2'b00,
    BUSY = 2'b01,
    NONSEQUENTIAL = 2'b10,
    SEQUENTIAL = 2'b11
  } htrans_types;

  logic        HCLK;
  logic        HRESETn;
  logic [31:0] HADDR;
  logic [ 1:0] HTRANS;
  logic [31:0] HWDATA;
  logic        HWRITE;
  logic        HSEL;
  logic        HREADY;
  logic        HREADYOUT;
  logic [31:0] HRDATA;

  logic [16:0] GPIOIN;
  logic [16:0] GPIOOUT;

  modport DUT
  ( input HCLK, HRESETn, HADDR, HTRANS, HWDATA, HWRITE, HSEL, HREADY, GPIOIN,
    output HREADYOUT, HRDATA, GPIOOUT
  );

  modport TB
  ( input HCLK, HREADYOUT, HRDATA, GPIOOUT,
    output HRESETn, HREADY, HADDR, HTRANS, HWDATA, HWRITE, HSEL, GPIOIN
  );
endinterface

module ahb_gpio_tb;
  localparam [7:0] gpio_data_addr = 8'h00;
  localparam [7:0] gpio_dir_addr = 8'h04;
  localparam max_test_count = 1000;

  logic parity_sel = '0;
  logic parity_err;
  integer test_count;

  ahb_gpio_if gpioif();
  AHBGPIO gpio(
      .HCLK         (gpioif.HCLK),
      .HRESETn      (gpioif.HRESETn),
      .HADDR        (gpioif.HADDR),
      .HTRANS       (gpioif.HTRANS),
      .HWDATA       (gpioif.HWDATA),
      .HWRITE       (gpioif.HWRITE),
      .HSEL         (gpioif.HSEL),
      .HREADY       (gpioif.HREADY),
      .GPIOIN       (gpioif.GPIOIN),
      .PARITYSEL    (parity_sel),
      .INJECT_FAULT ('0),
      .HREADYOUT    (gpioif.HREADYOUT),
      .HRDATA       (gpioif.HRDATA),
      .GPIOOUT      (gpioif.GPIOOUT),
      .PARITYERR    (parity_err)
  );

  ahb_gpio_checker gpio_checker(
      .HCLK         (gpioif.HCLK),
      .HRESETn      (gpioif.HRESETn),
      .HADDR        (gpioif.HADDR),
      .HTRANS       (gpioif.HTRANS),
      .HWDATA       (gpioif.HWDATA),
      .HWRITE       (gpioif.HWRITE),
      .HSEL         (gpioif.HSEL),
      .HREADY       (gpioif.HREADY),
      .GPIOIN       (gpioif.GPIOIN),
      .HREADYOUT    (gpioif.HREADYOUT),
      .HRDATA       (gpioif.HRDATA),
      .GPIOOUT      (gpioif.GPIOOUT),
      .PARITYERR    (parity_err),
      .PARITYSEL    (parity_sel)
  );

  class gpio_stimulus;
    rand logic        HSEL;
    rand logic        HWRITE;
    rand logic        HREADY;
    rand logic [ 1:0] HTRANS;
    rand logic [31:0] HWDATA;
    rand logic [31:0] HADDR;
    rand logic [16:0] GPIOIN;

    logic [31:0]      prev_haddr = '0;


    constraint c_hsel
    { HSEL dist { 1 :=99, 0:=1 }; }
    constraint c_hready
    { HREADY dist { 1 :=99, 0:=1 }; }
    constraint c_htrans
    { HTRANS dist { 2'b10 :=90, HTRANS :=10};}
    constraint c_haddr
    { HSEL -> HADDR dist {gpio_data_addr:=40, gpio_dir_addr:=40, HADDR:=20};}
    constraint c_gpio_dir_write
    {
      (prev_haddr[7:0]==gpio_dir_addr) -> (HWDATA==32'h0000 || HWDATA ==32'h0001);
    }
    constraint c_gpioin_parity
    { GPIOIN[16] == ~^{GPIOIN[15:0],parity_sel};}

    function void post_randomize;
      prev_haddr = HADDR;
    endfunction
  endclass

  gpio_stimulus stimulus_vals;

  covergroup cover_ahb_transaction_vals;
    cp_hsel: coverpoint gpioif.HSEL{
      bins hi = {1};
      bins lo = {0};
    }
    cp_hready: coverpoint gpioif.HREADY{
      bins hi = {1};
      bins lo = {0};
    }
    cp_hwrite: coverpoint gpioif.HWRITE{
      bins write = {1};
      bins read  = {0};
    }
    cp_haddr:  coverpoint gpioif.HADDR {
      bins data_addr 		= {gpio_data_addr};
      bins dir_addr  		= {gpio_dir_addr};
      bins invalid_addr 	= default;
    }
    cp_ahb_transaction: cross cp_hsel, cp_hready, cp_hwrite, cp_haddr {
      bins ahb_write = cp_ahb_transaction with (cp_hsel==1 && cp_hready==1 && cp_hwrite==1 && cp_haddr==gpio_data_addr);
      bins ahb_read  = cp_ahb_transaction with (cp_hsel==1 && cp_hready==1 && cp_hwrite==0);
      bins ahb_dir   = cp_ahb_transaction with (cp_hsel==1 && cp_hready==1 && cp_hwrite==1 && cp_haddr==gpio_dir_addr);
      ignore_bins ignore_invalid = cp_ahb_transaction with (cp_hsel!=1);
    }

  endgroup

  covergroup cover_hwdata_values;
    coverpoint gpioif.HWDATA;
  endgroup

  covergroup cover_hrdata_values;
    coverpoint gpioif.HRDATA[15:0];
  endgroup

  covergroup cover_gpio_in_values;
    coverpoint gpioif.GPIOIN[15:0];
  endgroup

  covergroup cover_gpio_out_values;
    coverpoint gpioif.GPIOOUT[15:0];
  endgroup

  task deassert_reset();
  begin
    gpioif.HRESETn = 0;
    @(posedge gpioif.HCLK);
    @(posedge gpioif.HCLK);
    gpioif.HRESETn = 1;
  end
  endtask

  initial begin
    cover_hwdata_values covhwdata;
    cover_hrdata_values covhrdata;
    cover_gpio_in_values covgpioin;
    cover_gpio_out_values covgpioout;
    cover_ahb_transaction_vals covahbtransactionvals;
    covhwdata   	          = new();
    covhrdata     	        = new();
    covgpioin    	          = new();
    covgpioout     	        = new();
    covahbtransactionvals   = new();
    stimulus_vals 	        = new();
    deassert_reset();

    for(test_count = 0; test_count < max_test_count;test_count++)
    begin
      assert (stimulus_vals.randomize) else $fatal;
      gpioif.HSEL  = stimulus_vals.HSEL;
      gpioif.HWRITE  = stimulus_vals.HWRITE;
      gpioif.HREADY   = stimulus_vals.HREADY;
      gpioif.HTRANS  = stimulus_vals.HTRANS;
      gpioif.HWDATA  = stimulus_vals.HWDATA;
      gpioif.HADDR  = stimulus_vals.HADDR;
      gpioif.GPIOIN  = stimulus_vals.GPIOIN;

      covhwdata.sample();
      covgpioin.sample();
      covhrdata.sample();
      covgpioout.sample();

      covahbtransactionvals.sample();

    @(posedge gpioif.HCLK);
    end
    @(posedge gpioif.HCLK);
    $finish;
  end
  initial begin
    gpioif.HCLK = 0;
    forever #1 gpioif.HCLK = ! gpioif.HCLK;
  end
endmodule