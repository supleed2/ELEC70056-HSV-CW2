# Verification Plan

This is a list of things that need testing and how they will be tested.

## GPIO

- Add parity bit generation to GPIO output
  - Fault injection signal included in parity bit output
  - Parity mode (even/odd) selectable using module input `PARITYSEL`
- Add parity bit checking to GPIO input
  - Fault injection signal included in `PARITYERR` generation
- Assertions used in formal verification using JasperGold
  - `assert_gpio_write`: AHB writes to the module result in correct GPIO bus output (including parity), when direction register is set correctly
  - `assert_gpio_read`: AHB reads return the correct data (matching the GPIO bus), when direction register is set correctly
  - `assert_gpio_dir`: AHB writes to the direction register correctly update the direction register
  - `assume_initial_valid`: Prevents JasperGold from initialising the direction register in an impossible state
  - `assume_gpio_in_valid_parity`: Assumes the GPIO input is not corrupt, for simplicity of testing
- GPIO Checker
  - Non-synthesizable version of GPIO which emulates the behaviour of the module, as a reference to check GPIO outputs
  - Contains assertions to verify correct changes in GPIO bus during a write and correct data on AHB bus during a read
- Constrained random unit-level testbench
  - Using a class `gpio_stimulus` with constraints on each of the input signals to the GPIO block
  - Cover groups to check that the desired values / edge-cases are simulated

## VGA

- Dual lock-step
  - Instantiate a second copy of the VGA module as `uAHBVGA2`
  - Comparator block `VGACOMPARATOR`
    - Single output that goes high if any signals do not match between the two VGA blocks
  - VGA image buffer is initialised on startup of testbench to prevent issues when comparing X outputs
- Debug image output
  - Renders a 1 bit image of the VGA frame as output on the RGB pin, in the simulation log file using `$display`
- Assertions used in formal verification using JasperGold
  - `assert_display_range_x`: Ensures X pixel counter is always within the frame boundary (display area)
  - `assert_display_range_y`: Ensures Y pixel counter is always within the frame boundary (display area)
  - `assert_vsync_pulse_timer`: Ensures correct width of VSYNC pulse
  - `assert_hsync_pulse_timer`: Ensures correct width of HSYNC pulse
  - `assert_line_timer`: Ensures the correct timing between consecutive HSYNC pulses / correct frame width timing
  - `assert_frame_timer`: Ensures the correct timing between consecutive VSYNC pulses / correct frame height timing
- VGA Checker
  - Non-synthesizable version of VGA which emulates the behaviour of the module, as a reference to check VGA outputs
  - Contains similar assertions as the planned formal verification, to be run during simulation
- Constrained random unit-level testbench
  - Using a class `vga_stimulus` with constraints on the input data to the VGA block
  - Cover groups to check that the desired values / edge-cases are simulated

## Top-level

- Assembly code to test GPIO
- Assembly code to test VGA
- C code to be compiled to assembly in Keil and tested on the instanced ARM core
