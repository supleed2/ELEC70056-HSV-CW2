module ahb_vgasys_checker(
  input wire HCLK,
  input wire HRESETn,
  input wire [31:0] HADDR,
  input wire [31:0] HWDATA,
  input wire HREADY,
  input wire HWRITE,
  input wire [1:0] HTRANS,
  input wire HSEL,
  input wire [31:0] HRDATA,
  input wire HREADYOUT,
  input wire HSYNC,
  input wire VSYNC,
  input wire [7:0] RGB,
  output wire [7:0] checker_rgb_out
);
  import ahb_vga_font_map::*;
  // NOTE: Due to a BUG in the VGA module, the first 2 pixels for each row in the visible region is invalid, the actual image starts 2 cycles later
  localparam text_region_x_min = 48 + 2;
  localparam text_region_x_max = text_region_x_min + 240 - 2;
  localparam text_region_y_min = 29;
  localparam text_region_y_max = text_region_y_min + 480;
  localparam character_width = 8;
  localparam character_height = 16;
  localparam characters_per_row = 240/character_width;
  localparam characters_per_col = 480/character_height;

  logic [31:0] counter;
  logic countup;
  int 	        pixel_x;
  int 	        pixel_y;
  //local coords within the visible text region
  int           frame_x;
  int           frame_y;
  //local coords within the tile
  logic [2:0]   character_x;
  logic [3:0]   character_y;

  logic [7:0]   checker_rgb;
  logic [7:0]   character_buffer[characters_per_row*characters_per_col];
  string        console_text_reg;

  int           hcounter;
  int           vcounter;


  function logic inTextRegion(int x, int y);
    return (x >= text_region_x_min && x <= text_region_x_max) && (y >= text_region_y_min && y <= text_region_y_max);
  endfunction

  function int getStringIndex(int x, int y);
    return (((y/character_height)*characters_per_row)+ (x/character_width));
  endfunction

  function logic[7:0] getRGBvalue(logic[2:0] x, logic[3:0] y, int char_index);
    return font_lookup({char_index, y})[7-x] ? 8'h1c : 8'h00;
  endfunction

  always_ff @(posedge HCLK)
  begin
    if(!HRESETn || !VSYNC)
    begin
      pixel_x           <= 0;
      pixel_y           <= 0;
      if(!HRESETn)
        console_text_reg  <= "";
        counter           <= 0;
      countup           <= 0;
    end
    else
    begin
      countup <= countup + 1;
      if($past(HSEL && HREADY && HWRITE && (HADDR[23:0]== 12'h000000000000),1) && HREADYOUT)
      begin
        console_text_reg          <= {console_text_reg,font_map[HWDATA]};
        character_buffer[counter] <= HWDATA[7:0];
        counter                   <= counter+1;
      end
      if($fell(vgaif.HSYNC))
      begin
        pixel_x           <= 0;
        pixel_y           <= pixel_y + 1;
      end
      else
      begin
        if(vgaif.HSYNC)
          if(countup)
          begin
            pixel_x         <= pixel_x + 1;
          end
      end
    end
  end

  always_ff @(posedge HCLK)
  begin
    if(!HRESETn)
    begin
      hcounter <= 0;
      vcounter <= 0;
    end
    else
    begin
      if($fell(VSYNC))
        vcounter <= 0;
      else
        if($fell(HSYNC))
          vcounter <= vcounter + 1;
      if($fell(HSYNC))
        hcounter <= 0;
      else
        hcounter <= hcounter + 1;
    end
  end

  always_comb
  begin
      checker_rgb   = 0;
      frame_x       = pixel_x - text_region_x_min;
      frame_y       = pixel_y - text_region_y_min;
      character_x   = frame_x % character_width;
      character_y   = frame_y % character_height;
      if(inTextRegion(pixel_x,pixel_y))
      begin
          if(getStringIndex(frame_x,frame_y) < console_text_reg.len())
          begin
            checker_rgb = getRGBvalue(character_x,character_y,character_buffer[getStringIndex(frame_x,frame_y)]);
            //$display("char: %s, x: 0x%0h, y: 0x%0h",console_text_reg.substr(getStringIndex(frame_x,frame_y),getStringIndex(frame_x,frame_y)),  frame_x, frame_y);
          end
      end
  end

  assign checker_rgb_out = checker_rgb;

  //assertions
  assert_text_region: assert property
  (
    @(posedge HCLK) disable iff (!HRESETn)
      (inTextRegion(pixel_x,pixel_y)  && (frame_x > 1)) -> (checker_rgb == RGB)
  );

  assert_vsync_pulse_timer: assert property
  (
    @(posedge HCLK) disable iff (!HRESETn)
    $rose(VSYNC) -> (($past(vcounter,1) == 8'h1) || (vcounter == '0))
  );

  assert_hsync_pulse_timer: assert property
  (
    @(posedge HCLK) disable iff (!HRESETn)
    ($rose(HSYNC) && !$rose(VSYNC) && VSYNC) -> ($past(hcounter,1)/2 == 8'd95)
  );

  assert_line_timer: assert property
  (
    @(posedge HCLK) disable iff (!HRESETn)
    ($fell(HSYNC) && !$rose(VSYNC) && VSYNC) -> ($past(hcounter,1)/2 == 800)
  );

  assert_frame_timer: assert property
  (
    @(posedge HCLK) disable iff (!HRESETn)
    $fell(VSYNC) -> (($past(vcounter,1) == (32'd480 + 32'd10 + 32'd2 + 32'd29)) || (vcounter == '0))
  );

endmodule