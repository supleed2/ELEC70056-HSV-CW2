gpio:
	vlog -work work +acc=blnr +cover -noincr -timescale 1ns/1ps rtl/**/*.sv tbench/*.sv
	vopt -work work ahb_gpio_tb -o work_opt
	vsim -coverage work_opt -do setup.do -l sim.log

vga:
	vlog -work work +acc=blnr +cover -noincr -timescale 1ns/1ps rtl/**/*.sv tbench/*.sv
	vopt -work work ahb_vga_tb -o work_opt
	vsim -coverage work_opt -do setup.do -l sim.log

sys:
	vlog -work work +acc=blnr -noincr -timescale 1ns/1ps rtl/**/*.sv tbench/*.sv
	vopt -work work ahblite_sys_tb -o work_opt
	vsim work_opt -do setup.do -l sim.log

# jg:
# 	jg rtl/AHB_GPIO/AHBGPIO.tcl
