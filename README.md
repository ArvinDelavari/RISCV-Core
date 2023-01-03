# RISCV CORE - RV32I

## RISC-V CPU Design using TL-Verilog in Makerchip IDE :
- Design of a simple 32-bit RISC-V CPU using the base instruction set, RV32I (+5 stage pipeline).
- Hardware description was done with TL-Verilog(Transaction Level Verilog)  using Makerchip IDE, which gives a better sense of timing abstraction.
- You can simulate this RISC-V processors on Linux using GCC Compiler toolchain and iVerilog tool, using Verilog output of Makerchip IDE.
- Updates and new features will be added to the CPU; this file is a simple base microprocessor.
## Verilog output and simulations
- This repository includes Verilog files for macros used in TL-Verilog code and the main CPU code("RV32I CORE - Verilog" folder). 
- System-Verilog is also supported in Makerchip IDE; so you can add other functions to the CPU TL-Verilog file in repository.
- You can use the .v output to run C codes on the cpu using iverilog software in Linux.
## Program simulations
- This RISC-V CPU executes a simple code in C (using iverilog software in Linux) as an example task.
- You can see RISC-V assembly instructions running on the CPU in VIZ tab in Makerchip IDE after compiling the code.
- The code is "sum of 1 to n" for n=100. It takes 561 clock cycles for 304 instructions, which  gives us a CPI near 1.8 (close to standard RISC processors, nearly 1.4).
- You can use run.sh to install RISC-V toolchain and GCC compiler. You need to install GCC compiler before running this shell-script(32/64bit). By using this toolchain you can compile C codes for RISC-V CPU to simulate them on iverilog software. You can also checkout assembly output of your code and use them for ABI.

## Arvin Delavari - Faraz Ghoreishy 
### Iran University of Science and Technology
