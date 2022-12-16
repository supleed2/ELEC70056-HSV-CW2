clear -all
analyze -clear
analyze -sv rtl/AHB_VGA/AHBVGASYS_SVA.sv rtl/AHB_VGA/counter.sv rtl/AHB_VGA/dual_port_ram_sync.sv rtl/AHB_VGA/font_rom.sv rtl/AHB_VGA/vga_console.sv rtl/AHB_VGA/vga_image.sv rtl/AHB_VGA/vga_sync.sv
elaborate -bbox_mul 64 -top AHBVGA_SVA

clock HCLK
reset -expression !(HRESETn)

task -set <embedded>
set_proofgrid_max_jobs 4
set_proofgrid_max_local_jobs 4