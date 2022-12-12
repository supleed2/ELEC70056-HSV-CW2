// stub
interface ahb_vga_if;

  typedef enum bit[1:0] {
    IDLE = 2'b00,
    BUSY = 2'b01,
    NONSEQUENTIAL = 2'b10,
    SEQUENTIAL = 2'b11
  } htrans_types;

  logic        	HCLK;
  logic        	HRESETn;
  logic [31:0] 	HADDR;
  logic [ 1:0] 	HTRANS;
  logic [31:0] 	HWDATA;
  logic        	HWRITE;
  logic        	HSEL;
  logic        	HREADY;
  logic        	HREADYOUT;
  logic [31:0] 	HRDATA;

  logic [7:0]  	RGB;
  logic 	   	HSYNC;
  logic 	   	VSYNC;


  modport DUT
  ( input HCLK, HRESETn, HADDR, HTRANS, HWDATA, HWRITE, HSEL, HREADY,
    output HREADYOUT, HRDATA, RGB, HSYNC, VSYNC
  );

  modport TB
  ( input HCLK, HREADYOUT, HRDATA, RGB, HSYNC, VSYNC,
    output HRESETn, HREADY, HADDR, HTRANS, HWDATA, HWRITE, HSEL
  );
endinterface

module ahb_vga_tb;
  import ahb_vga_font_map::*;
  localparam IMAGEADDR = 4'hA;
  localparam CONSOLEADDR = 4'h0;

	ahb_vga_if vgaif();
	AHBVGA vga(
		.HCLK(vgaif.HCLK),
		.HRESETn(vgaif.HRESETn),
		.HADDR(vgaif.HADDR),
		.HWDATA(vgaif.HWDATA),
		.HREADY(vgaif.HREADY),
		.HWRITE(vgaif.HWRITE),
		.HTRANS(vgaif.HTRANS),
		.HSEL(vgaif.HSEL),
		.HRDATA(vgaif.HRDATA),
		.HREADYOUT(vgaif.HREADYOUT),
		.HSYNC(vgaif.HSYNC),
		.VSYNC(vgaif.VSYNC),
		.RGB(vgaif.RGB)
	);

  logic [7:0] checker_rgb;
  ahb_vgasys_checker vga_checker(
		.HCLK(vgaif.HCLK),
		.HRESETn(vgaif.HRESETn),
		.HADDR(vgaif.HADDR),
		.HWDATA(vgaif.HWDATA),
		.HREADY(vgaif.HREADY),
		.HWRITE(vgaif.HWRITE),
		.HTRANS(vgaif.HTRANS),
		.HSEL(vgaif.HSEL),
		.HRDATA(vgaif.HRDATA),
		.HREADYOUT(vgaif.HREADYOUT),
		.HSYNC(vgaif.HSYNC),
		.VSYNC(vgaif.VSYNC),
		.RGB(vgaif.RGB),
    .checker_rgb_out(checker_rgb)
  );

  logic display_enable;
  integer reset_time;
  task deassert_reset();
  begin
    vgaif.HRESETn = 0;
    @(posedge vgaif.HCLK);
    @(posedge vgaif.HCLK);
    vgaif.HRESETn = 1;
  end
  endtask
  initial begin
    vgaif.HCLK = 0;
    forever #20 vgaif.HCLK = ! vgaif.HCLK;
  end

  string line;

  always @(posedge vgaif.HCLK) begin
    if(display_enable)
      if ($fell(vgaif.HSYNC)) begin
          $display(line);
          line = "";
      end else if (vgaif.HSYNC)
        if (checker_rgb == 8'd28)
          line = {line, "#"};
        else
          line = {line, "."};
  end

  task setChar(input bit [7:0] c);
    @(posedge vgaif.HCLK);
    vgaif.HREADY = 1;
    vgaif.HWRITE = 1;
    vgaif.HTRANS = 2'b10;
    vgaif.HSEL = 1;
    vgaif.HADDR = 32'h50000000;
    @(posedge(vgaif.HCLK));
    vgaif.HWDATA = c;
    vgaif.HWRITE = 0;
    @(posedge (vgaif.HCLK && vgaif.HREADYOUT));
  endtask

  class vga_stimulus;
    randc logic [31:0] HWDATA;

    constraint c_hwdata
    {0 <= HWDATA; HWDATA <= 8'h7f;}
  endclass

  vga_stimulus stimulus_vals;

  covergroup cover_vga_chars;
    cp_hwdata: coverpoint vgaif.HWDATA{
      bins lo_1   = {[0:15]};
      bins lo_2   = {[16:31]};
      bins mid_1  = {[32:47]};
      bins mid_2  = {[48:63]};
      bins mid_3  = {[64:79]};
      bins mid_4  = {[80:95]};
      bins hi_1   = {[96:111]};
      bins hi_2   = {[112:127]};
    }
  endgroup


  integer char_index;
  string test_value = "";
  initial begin
    cover_vga_chars covvgachars;
    covvgachars = new();
    stimulus_vals = new();
    display_enable = 0;
    deassert_reset();
    display_enable = 1;
    test_value = "";
    @(posedge vgaif.VSYNC);
    display_enable = 1;
    $display(test_value);
    for(char_index = 0; char_index < 30; char_index++)
    begin

      assert (stimulus_vals.randomize) else $fatal;
      setChar(stimulus_vals.HWDATA);
      covvgachars.sample();
      test_value = {test_value, font_map[stimulus_vals.HWDATA]};
    end
    // setChar(8'h08);
    // setChar(8'h54);
    // setChar(8'h45);
    // setChar(8'h53);
    // setChar(8'h54);
    // setChar(8'h21);
    // setChar(8'h00);
    vgaif.HREADY = '0;
    vgaif.HWRITE = '0;
    vgaif.HTRANS = '0;
    vgaif.HSEL   = '0;
    vgaif.HADDR  = '0;
    vgaif.HWDATA = '0;
    @(posedge vgaif.VSYNC);
    $display(test_value);
    $stop;
  end

  logic rgb_active;
  assign rgb_active = (vgaif.RGB==8'h1c);
  logic checker_rgb_active;
  assign checker_rgb_active = (checker_rgb==8'h1c);

endmodule