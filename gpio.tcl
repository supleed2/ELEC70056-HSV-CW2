clear -all
analyze -clear
analyze -sv rtl/AHB_GPIO/AHBGPIO_SVA.sv
elaborate -bbox_mul 64 -top AHBGPIO_SVA

clock HCLK
reset -expression !(HRESETn)

task -set <embedded>
set_proofgrid_max_jobs 4
set_proofgrid_max_local_jobs 4
