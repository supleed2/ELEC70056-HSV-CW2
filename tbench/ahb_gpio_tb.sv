//stub
interface ahb_gpio_if;

	typedef enum bit[1:0] {
		IDLE = 2'b00,
		BUSY = 2'b01,
		NONSEQUENTIAL = 2'b10,
		SEQUENTIAL = 2'b11
	} htrans_types;

	logic 			HCLK;
	logic 			HRESETn;
	logic [31:0]	HADDR;
	logic [1:0]	    HTRANS;
	logic [31:0]	HWDATA;
	logic 			HWRITE;
	logic 			HSEL;
	logic 			HREADY;
	logic 			HREADYOUT;
	logic [31:0]	HRDATA;

	logic [15:0]	GPIOIN;
	logic [15:0]	GPIOOUT;

	modport	DUT	(input HCLK, HRESETn, HADDR, HTRANS, HWDATA, HWRITE, HSEL, HREADY, GPIOIN,
				 output HREADYOUT, HRDATA, GPIOOUT);

	modport  TB (input HCLK, HREADYOUT, HRDATA, GPIOOUT,
				output HRESETn, HREADY, HADDR, HTRANS, HWDATA, HWRITE, HSEL, GPIOIN);
endinterface


program automatic ahb_gpio_tb
	(ahb_gpio_if.TB gpioif);

  	localparam [7:0] gpio_data_addr = 8'h00;
  	localparam [7:0] gpio_dir_addr = 8'h04;
	localparam max_test_count = 1000;
	integer test_count;

	class gpio_stimulus;
		typedef enum bit[1:0] {
			GPIO_WRITE = 2'b00,
			GPIO_READ  = 2'b01,
			GPIO_DIR   = 2'b10,
			RANDOM     = 2'b11
		} stimulus_op;
		rand stimulus_op gpio_op;

		rand logic 			HSEL;
		rand logic 			HWRITE;
		rand logic 			HREADY;
		rand logic [1:0]	HTRANS;

		rand logic [31:0] 	HWDATA;
		rand logic [31:0] 	HADDR;

		rand logic [15:0] 	GPIOIN;

		constraint c_haddr {((gpio_op == GPIO_WRITE) && (HADDR == gpio_data_addr)) ||
							((gpio_op == GPIO_DIR) && (HADDR == gpio_dir_addr)) ||
							(gpio_op == GPIO_READ) ||
							(gpio_op == RANDOM);}

		constraint c_write {((gpio_op == GPIO_WRITE)|| (gpio_op == GPIO_DIR)) -> (HSEL && HWRITE && HREADY && (HTRANS == 2'b10));}

		constraint c_read  {(gpio_op == GPIO_READ)  -> (HSEL && !HWRITE && HREADY);}
	endclass

	gpio_stimulus stimulus_vals;

	covergroup cover_addr_values;
		coverpoint gpioif.HADDR {
			bins data_addr 		= {gpio_data_addr};
			bins dir_addr  		= {gpio_dir_addr};
			bins invalid_addr 	= default;
		}
	endgroup

	covergroup cover_wr_vals;
		coverpoint {HSEL,HWRITE,HREADY} {
			bins write 			= {{1,1,1}};
			bins read 			= {{1,0,1}};
			bins invalid 		= default;
		}
	endgroup

	covergroup cover_ahb_write_values;
		coverpoint gpioif.HWDATA {
			bins zero = {0};
			bins lo   = {[1:7]};
			bins med  = {[8:23]};
			bins hi   = {[24:30]};
			bins max  = {32'hFFFF};
		}
	endgroup

	covergroup cover_ahb_read_values;
		coverpoint gpioif.HRDATA {
			bins zero = {0};
			bins lo   = {[1:7]};
			bins med  = {[8:23]};
			bins hi   = {[24:30]};
			bins max  = {32'hFFFF};
		}
	endgroup

	covergroup cover_gpio_in_values;
		coverpoint gpioif.GPIOIN {
			bins zero = {0};
			bins lo   = {[1:4]};
			bins med  = {[5:9]};
			bins high = {[10:14]};
			bins max  = {16'hFF};
		}
	endgroup

	covergroup cover_gpio_out_values;
		coverpoint gpioif.GPIOOUT {
			bins zero = {0};
			bins lo   = {[1:4]};
			bins med  = {[5:9]};
			bins high = {[10:14]};
			bins max  = {16'hFF};
		}
	endgroup
	task deassert_reset();
	begin
		gpioif.HRESETn = 0;
		@(posedge gpioif.HCLK);
		@(posedge gpioif.HCLK);
		gpioif.HRESETn = 1;
		@(posedge gpioif.HCLK);
	end
	endtask

	initial begin
		cover_addr_values covaddr;
		cover_ahb_write_values covahbwrite;
		cover_ahb_read_values covahbread;
		cover_gpio_in_values covgpioin;
		cover_gpio_out_values covgpioout;
		covaddr 		= new();
		covahbwrite 	= new();
		covahbread 		= new();
		covgpioin		= new();
		covgpioout 		= new();

		deassert_reset();

		for(test_count = 0; test_count < max_test_count;test_count++)
		begin
			@(posedge gpioif.HCLK);
			assert (stimulus_vals.randomize) else $fatal;
			gpioif.HSEL	= stimulus_vals.HSEL;
			gpioif.HWRITE	= stimulus_vals.HWRITE;
			gpioif.HREADY 	= stimulus_vals.HREADY;
			gpioif.HTRANS	= stimulus_vals.HTRANS;
			gpioif.HWDATA	= stimulus_vals.HWDATA;
			gpioif.HADDR	= stimulus_vals.HADDR;
			gpioif.GPIOIN	= stimulus_vals.GPIOIN;

				covaddr.sample();
				covahbwrite.sample();
				covgpioin.sample();
				covahbread.sample();
				covgpioout.sample();
		end
		@(posedge gpioif.HCLK);
		$finish;
	end
endprogram