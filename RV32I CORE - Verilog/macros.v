`line 2 "top.tlv" 0 //_\TLV_version 1d: tl-x.org, generated by SandPiper(TM) 1.14-2022/10/10-beta-Pro
//_\SV
  
   // Included URL: "https://raw.githubusercontent.com/stevehoover/RISC-V_MYTH_Workshop/c1719d5b338896577b79ee76c2f443ca2a76e14f/tlv_lib/risc-v_shell_lib.tlv"// Included URL: "https://raw.githubusercontent.com/stevehoover/warp-v_includes/2d6d36baa4d2bc62321f982f78c8fe1456641a43/risc-v_defs.tlv"

//_\SV
   module top(input wire clk, input wire reset, input wire [31:0] cyc_cnt, output wire passed, output wire failed);    /* verilator lint_save */ /* verilator lint_off UNOPTFLAT */  bit [256:0] RW_rand_raw; bit [256+63:0] RW_rand_vect; pseudo_rand #(.WIDTH(257)) pseudo_rand (clk, reset, RW_rand_raw[256:0]); assign RW_rand_vect[256+63:0] = {RW_rand_raw[62:0], RW_rand_raw};  /* verilator lint_restore */  /* verilator lint_off WIDTH */ /* verilator lint_off UNOPTFLAT */   // (Expanded in Nav-TLV pane.)
`include "top_gen.sv" //_\TLV

   
   // Program for MYTH Workshop to test RV32I
   // Add 1,2,3,...,9 .
   //
   // Regs:
   //  r10 (a0): In: 0, Out: final sum
   //  r12 (a2): 10
   //  r13 (a3): 1..10
   //  r14 (a4): Sum
   // 
   // External to function:
   // Inst #0: ADD,r10,r0,r0             // Initialize r10 (a0) to 0.
   // Function:
   // Inst #1: ADD,r14,r10,r0            // Initialize sum register a4 with 0x0
   // Inst #2: ADDI,r12,r10,1010         // Store count of 10 in register a2.
   // Inst #3: ADD,r13,r10,r0            // Initialize intermediate sum register a3 with 0
   // Loop:
   // Inst #4: ADD,r14,r13,r14           // Incremental addition
   // Inst #5: ADDI,r13,r13,1            // Increment intermediate register by 1
   // Inst #6: BLT,r13,r12,1111111111000 // If a3 is less than a2, branch to label named <loop>
   // Inst #7: ADD,r10,r14,r0            // Store final result to register a0 so that it can be read by main program
   
   // Inst #8: SW,r0,r10,100
   // Inst #9: LW,r17,r0,100
   
   
   
   assign L0_passed_a0 = passed ;
   
   //_|cpu
      //_@0
         assign CPU_reset_a0 = reset;
         //$inv_reset = ! $reset;
         
         assign CPU_pc_a0[31:0] = CPU_reset_a1 ? 0 : 
                     CPU_valid_taken_br_a3 ? CPU_br_tgt_pc_a3 : 
                     CPU_valid_load_a3 ? CPU_incr_pc_a3 : 
                     (CPU_valid_jump_a3 && CPU_is_jal_a3) ? CPU_br_tgt_pc_a3 : 
                     (CPU_valid_jump_a3 && CPU_is_jalr_a3) ? CPU_jalr_tgt_pc_a3 : 
                     CPU_incr_pc_a1; //Program Counter
         
         //$start = $reset ? 0 : ( $reset ^ >>1$reset ) ;
         //$valid = $reset ? 0 : $start ? $start : >>3$valid ;
         
         //?$inv_reset
         assign CPU_imem_rd_en_a0 = !CPU_reset_a0;
         assign CPU_imem_rd_addr_a0[4-1:0] = CPU_pc_a0[4+1:2];
            
      //_@1
         //?$inv_reset
         assign CPU_instr_a1[31:0] = CPU_imem_rd_data_a1;
         assign CPU_incr_pc_a1[31:0] = CPU_pc_a1 + 32'd4 ;
         
         //Decode
         //Instruction Type
         assign CPU_is_i_instr_a1 = CPU_instr_a1[6:2] ==? 5'b0000x || 
                       CPU_instr_a1[6:2] ==? 5'b001x0 || 
                       CPU_instr_a1[6:2] ==? 5'b11001;
         
         assign CPU_is_u_instr_a1 = CPU_instr_a1[6:2] ==? 5'b0x101;
         
         assign CPU_is_s_instr_a1 = CPU_instr_a1[6:2] ==? 5'b0100x;
         
         assign CPU_is_r_instr_a1 = CPU_instr_a1[6:2] ==? 5'b01011 || 
                       CPU_instr_a1[6:2] ==? 5'b10100 || 
                       CPU_instr_a1[6:2] ==? 5'b011x0;
         
         assign CPU_is_b_instr_a1 = CPU_instr_a1[6:2] ==? 5'b11000;
         
         assign CPU_is_j_instr_a1 = CPU_instr_a1[6:2] ==? 5'b11011; 
         
         assign CPU_imm_a1[31:0] = CPU_is_i_instr_a1 ? {{21{CPU_instr_a1[31]}}, CPU_instr_a1[30:20]} :
                      CPU_is_s_instr_a1 ? {{21{CPU_instr_a1[31]}}, CPU_instr_a1[30:25], CPU_instr_a1[11:7]} :
                      CPU_is_b_instr_a1 ? {{20{CPU_instr_a1[31]}}, CPU_instr_a1[7], CPU_instr_a1[30:25], CPU_instr_a1[11:8],1'b0} :
                      CPU_is_u_instr_a1 ? {CPU_instr_a1[31:12], 12'h000} :
                      CPU_is_j_instr_a1 ? {{12{CPU_instr_a1[31]}}, CPU_instr_a1[19:12], CPU_instr_a1[20], CPU_instr_a1[30:21], 1'b0} : 32'h0 ;
         
         assign CPU_opcode_a1[6:0] = CPU_instr_a1[6:0];
         
         assign CPU_funct3_valid_a1 = CPU_is_r_instr_a1 || CPU_is_i_instr_a1 || CPU_is_s_instr_a1 || CPU_is_b_instr_a1 ;
         assign CPU_funct7_valid_a1 = CPU_is_r_instr_a1 ;
         assign CPU_rs1_valid_a1 = CPU_is_r_instr_a1 || CPU_is_i_instr_a1 || CPU_is_s_instr_a1 || CPU_is_b_instr_a1 ;
         assign CPU_rs2_valid_a1 = CPU_is_r_instr_a1 || CPU_is_s_instr_a1 || CPU_is_b_instr_a1 ;
         assign CPU_rd_valid_a1 = CPU_is_r_instr_a1 || CPU_is_i_instr_a1 || CPU_is_u_instr_a1 || CPU_is_j_instr_a1 ;
         
         //_?$funct3_valid
            assign CPU_funct3_a1[2:0] = CPU_instr_a1[14:12] ;
         
         //_?$funct7_valid
            assign CPU_funct7_a1[6:0] = CPU_instr_a1[31:25] ;
         
         //_?$rs1_valid
            assign CPU_rs1_a1[4:0] = CPU_instr_a1[19:15] ;
         
         //_?$rs2_valid
            assign CPU_rs2_a1[4:0] = CPU_instr_a1[24:20] ;
         
         //_?$rd_valid
            assign CPU_rd_a1[4:0] = CPU_instr_a1[11:7] ;
            
         //Individual Instr Decode
         assign CPU_dec_bits_a1[10:0] = { CPU_funct7_a1[5], CPU_funct3_a1, CPU_opcode_a1 } ;
         
         assign CPU_is_lui_a1   = CPU_dec_bits_a1 ==? 11'bx_xxx_0110111 ;
         assign CPU_is_auipc_a1 = CPU_dec_bits_a1 ==? 11'bx_xxx_0010111 ;
         
         assign CPU_is_jal_a1   = CPU_dec_bits_a1 ==? 11'bx_xxx_1101111 ;
         assign CPU_is_jalr_a1  = CPU_dec_bits_a1 ==? 11'bx_000_1100111 ;
         
         //Branch Instructions
         assign CPU_is_beq_a1   = CPU_dec_bits_a1 ==? 11'bx_000_1100011 ;
         assign CPU_is_bne_a1   = CPU_dec_bits_a1 ==? 11'bx_001_1100011 ;
         assign CPU_is_blt_a1   = CPU_dec_bits_a1 ==? 11'bx_100_1100011 ;
         assign CPU_is_bge_a1   = CPU_dec_bits_a1 ==? 11'bx_101_1100011 ;
         assign CPU_is_bltu_a1  = CPU_dec_bits_a1 ==? 11'bx_110_1100011 ;
         assign CPU_is_bgeu_a1  = CPU_dec_bits_a1 ==? 11'bx_111_1100011 ;
         
         //Load
         assign CPU_is_lb_a1    = CPU_dec_bits_a1 ==? 11'bx_000_0000011 ;
         assign CPU_is_lh_a1    = CPU_dec_bits_a1 ==? 11'bx_001_0000011 ;
         assign CPU_is_lw_a1    = CPU_dec_bits_a1 ==? 11'bx_010_0000011 ;
         assign CPU_is_lbu_a1   = CPU_dec_bits_a1 ==? 11'bx_100_0000011 ;
         assign CPU_is_lhu_a1   = CPU_dec_bits_a1 ==? 11'bx_101_0000011 ;
         
         //Store
         assign CPU_is_sb_a1    = CPU_dec_bits_a1 ==? 11'bx_000_0100011 ;
         assign CPU_is_sh_a1    = CPU_dec_bits_a1 ==? 11'bx_001_0100011 ;
         assign CPU_is_sw_a1    = CPU_dec_bits_a1 ==? 11'bx_010_0100011 ;
         
         assign CPU_is_addi_a1  = CPU_dec_bits_a1 ==? 11'bx_000_0010011 ;
         assign CPU_is_slti_a1  = CPU_dec_bits_a1 ==? 11'bx_010_0010011 ;
         assign CPU_is_sltiu_a1 = CPU_dec_bits_a1 ==? 11'bx_011_0010011 ;
         assign CPU_is_xori_a1  = CPU_dec_bits_a1 ==? 11'bx_100_0010011 ;
         assign CPU_is_ori_a1   = CPU_dec_bits_a1 ==? 11'bx_110_0010011 ;
         assign CPU_is_andi_a1  = CPU_dec_bits_a1 ==? 11'bx_111_0010011 ;
         assign CPU_is_slli_a1  = CPU_dec_bits_a1 ==? 11'b0_001_0010011 ;
         assign CPU_is_srli_a1  = CPU_dec_bits_a1 ==? 11'b0_101_0010011 ;
         assign CPU_is_srai_a1  = CPU_dec_bits_a1 ==? 11'b1_101_0010011 ;
         
         assign CPU_is_add_a1   = CPU_dec_bits_a1 ==? 11'b0_000_0110011 ;
         assign CPU_is_sub_a1   = CPU_dec_bits_a1 ==? 11'b1_000_0110011 ;
         assign CPU_is_sll_a1   = CPU_dec_bits_a1 ==? 11'b0_001_0110011 ;
         assign CPU_is_slt_a1   = CPU_dec_bits_a1 ==? 11'b0_010_0110011 ;
         assign CPU_is_sltu_a1  = CPU_dec_bits_a1 ==? 11'b0_011_0110011 ;
         assign CPU_is_xor_a1   = CPU_dec_bits_a1 ==? 11'b0_100_0110011 ;
         assign CPU_is_srl_a1   = CPU_dec_bits_a1 ==? 11'b0_101_0110011 ;
         assign CPU_is_sra_a1   = CPU_dec_bits_a1 ==? 11'b1_101_0110011 ;
         assign CPU_is_or_a1    = CPU_dec_bits_a1 ==? 11'b0_110_0110011 ;
         assign CPU_is_and_a1   = CPU_dec_bits_a1 ==? 11'b0_111_0110011 ;
         
         `BOGUS_USE(CPU_is_lui_a1 CPU_is_auipc_a1 CPU_is_jal_a1 CPU_is_jalr_a1 CPU_is_beq_a1 CPU_is_bne_a1 CPU_is_blt_a1 CPU_is_bge_a1 CPU_is_bltu_a1 CPU_is_bgeu_a1 CPU_is_lb_a1 CPU_is_lh_a1 CPU_is_lw_a1 CPU_is_lbu_a1 CPU_is_lhu_a1 CPU_is_sb_a1 CPU_is_sh_a1 CPU_is_sw_a1 CPU_is_addi_a1 CPU_is_slti_a1 CPU_is_sltiu_a1 CPU_is_xori_a1 CPU_is_ori_a1 CPU_is_andi_a1 CPU_is_slli_a1 CPU_is_srli_a1 CPU_is_srai_a1 CPU_is_add_a1 CPU_is_sub_a1 CPU_is_sll_a1 CPU_is_slt_a1 CPU_is_sltu_a1 CPU_is_xor_a1 CPU_is_srl_a1 CPU_is_sra_a1 CPU_is_or_a1 CPU_is_and_a1)
         
      //_@2
         //Read Reg File
         assign CPU_rf_rd_en1_a2 = CPU_rs1_valid_a2 ;
         //_?$rs1_valid
            assign CPU_rf_rd_index1_a2[4:0] = CPU_rs1_a2 ;
            
         assign CPU_src1_value_a2[31:0] = (CPU_rf_wr_en_a3 && (CPU_rd_a3 == CPU_rs1_a2)) ? CPU_result_a3 : CPU_rf_rd_data1_a2 ; //output 1
         
         assign CPU_rf_rd_en2_a2 = CPU_rs2_valid_a2 ;
         //_?$rs2_valid
            assign CPU_rf_rd_index2_a2[4:0] = CPU_rs2_a2 ;
            
         assign CPU_src2_value_a2[31:0] = (CPU_rf_wr_en_a3 && (CPU_rd_a3 == CPU_rs2_a2)) ? CPU_result_a3 : CPU_rf_rd_data2_a2 ; //output 2
         
         assign CPU_br_tgt_pc_a2[31:0] = CPU_pc_a2 + CPU_imm_a2 ;
         
      //_@3 
         assign CPU_sltu_rslt_a3 = CPU_src1_value_a3 < CPU_src2_value_a3 ;
         assign CPU_sltiu_rslt_a3 = CPU_src1_value_a3 < CPU_imm_a3 ;
         
         assign CPU_result_a3[31:0] = 
                 CPU_is_andi_a3 ? CPU_src1_value_a3 & CPU_imm_a3 :
                 CPU_is_ori_a3 ? CPU_src1_value_a3 | CPU_imm_a3 :
                 CPU_is_xori_a3 ? CPU_src1_value_a3 ^ CPU_imm_a3 :
                 CPU_is_addi_a3 ? CPU_src1_value_a3 + CPU_imm_a3 :
                 CPU_is_slli_a3 ? CPU_src1_value_a3 << CPU_imm_a3 :
                 CPU_is_srli_a3 ? CPU_src1_value_a3 >> CPU_imm_a3 :
                 CPU_is_and_a3 ? CPU_src1_value_a3 & CPU_src2_value_a3 :
                 CPU_is_or_a3 ? CPU_src1_value_a3 | CPU_src2_value_a3 :
                 CPU_is_xor_a3 ? CPU_src1_value_a3 ^ CPU_src2_value_a3 :
                 CPU_is_add_a3 ? CPU_src1_value_a3 + CPU_src2_value_a3 :
                 CPU_is_sub_a3 ? CPU_src1_value_a3 - CPU_src2_value_a3 :
                 CPU_is_sll_a3 ? CPU_src1_value_a3 << CPU_src2_value_a3 :
                 CPU_is_srl_a3 ? CPU_src1_value_a3 >> CPU_src2_value_a3 :
                 CPU_is_sltu_a3 ? CPU_sltu_rslt_a3 :
                 CPU_is_sltiu_a3 ? CPU_sltiu_rslt_a3 :
                 CPU_is_lui_a3 ? { CPU_imm_a3[31:12], 12'b0 } :
                 CPU_is_auipc_a3 ? CPU_pc_a3 + CPU_imm_a3 :
                 CPU_is_jal_a3 ? CPU_pc_a3 + 32'd4 :
                 CPU_is_jalr_a3 ? CPU_pc_a3 + 32'd4 :
                 CPU_is_srai_a3 ? { {32{CPU_src1_value_a3[31]}}, CPU_src1_value_a3 } >> CPU_imm_a3[4:0] :
                 CPU_is_slt_a3 ? (CPU_src1_value_a3[31] == CPU_src2_value_a3[31]) ? CPU_sltu_rslt_a3 : {31'b0, CPU_src1_value_a3[31]} :
                 CPU_is_slti_a3 ? (CPU_src1_value_a3[31] == CPU_imm_a3) ? CPU_sltiu_rslt_a3 : {31'b0, CPU_src1_value_a3[31]} :
                 CPU_is_sra_a3 ? { {32{CPU_src1_value_a3[31]}}, CPU_src1_value_a3 } >> CPU_src2_value_a3[4:0] :
                 32'bx;
         
         
         //Write Reg File
         //$rf_wr_en = $rd_valid && ($rd[4:0] != 5'b00000) && $valid;
         assign CPU_rf_wr_en_a3 = (CPU_rd_valid_a3 && (CPU_rd_a3[4:0] != 5'b00000) && CPU_valid_a3) || CPU_valid_load_a5;
         assign CPU_rf_wr_index_a3[4:0] = !(CPU_valid_load_a5) ? CPU_rd_a3 : CPU_rd_a5;
         assign CPU_rf_wr_data_a3[31:0] = !(CPU_valid_load_a5) ? CPU_result_a3 : CPU_ld_data_a5 ;
         
         //$value[31:0] = $rf_wr_data ;
         //$rf_wr_data[31:0] = $value ;
         //Branching
         assign CPU_taken_br_a3 = CPU_is_beq_a3 ? (CPU_src1_value_a3 == CPU_src2_value_a3) :
                     CPU_is_bne_a3 ? (CPU_src1_value_a3 != CPU_src2_value_a3) :
                     CPU_is_blt_a3 ? (CPU_src1_value_a3 < CPU_src2_value_a3) ^ (CPU_src1_value_a3[31] != CPU_src2_value_a3[31]) :
                     CPU_is_bge_a3 ? (CPU_src1_value_a3 >= CPU_src2_value_a3) ^ (CPU_src1_value_a3[31] != CPU_src2_value_a3[31]) :
                     CPU_is_bltu_a3 ? (CPU_src1_value_a3 < CPU_src2_value_a3) :
                     CPU_is_bgeu_a3 ? (CPU_src1_value_a3 >= CPU_src2_value_a3) : 1'b0 ;
         
         assign CPU_valid_taken_br_a3 = CPU_valid_a3 && CPU_taken_br_a3 ;
         
         assign CPU_valid_a3 = !( CPU_valid_taken_br_a4 || CPU_valid_taken_br_a5 || CPU_valid_load_a4 || CPU_valid_load_a5) ;
         
         assign CPU_is_load_a3 = CPU_is_lb_a3 || CPU_is_lh_a3 || CPU_is_lw_a3 || CPU_is_lbu_a3 || CPU_is_lhu_a3 ;
         //$is_store = $is_sb || $is_sh || $is_sw ;
         assign CPU_valid_load_a3 = CPU_valid_a3 && CPU_is_load_a3;
         
         assign CPU_is_jump_a3 = CPU_is_jal_a3 || CPU_is_jalr_a3 ;
         assign CPU_valid_jump_a3 = CPU_valid_a3 && CPU_is_jump_a3;
         assign CPU_jalr_tgt_pc_a3 = CPU_src1_value_a3 + CPU_imm_a3 ;
         
         
         
      //_@4
         //DMEM
         assign CPU_dmem_wr_en_a4 = CPU_is_s_instr_a4 && CPU_valid_a4 ;
         assign CPU_dmem_addr_a4[3:0] = CPU_result_a4[5:2] ;
         assign CPU_dmem_wr_data_a4[31:0] = CPU_src2_value_a4 ;
         assign CPU_dmem_rd_en_a4 = CPU_is_load_a4 ;
         //$dmem_rd_index[5:0] = ;
         
      //_@5
         assign CPU_ld_data_a5[31:0] = CPU_dmem_rd_data_a5 ;
         
      

      // YOUR CODE HERE
      // ...

      // Note: Because of the magic we are using for visualisation, if visualisation is enabled below,
      //       be sure to avoid having unassigned signals (which you might be using for random inputs)
      //       other than those specifically expected in the labs. You'll get strange errors for these.

   
   // Assert these to end simulation (before Makerchip cycle limit).
   //*passed = *cyc_cnt > 40;
   assign failed = 1'b0;
   assign passed = CPU_Xreg_value_a5[17] == (1+2+3+4+5+6+7+8+9);
   
   // Macro instantiations for:
   //  o instruction memory
   //  o register file
   //  o data memory
   //  o CPU visualization
   //_|cpu
      `line 17 "/raw.githubusercontent.com/stevehoover/RISCVMYTHWorkshop/c1719d5b338896577b79ee76c2f443ca2a76e14f/tlvlib/riscvshelllib.tlv" 1   // Instantiated from top.tlv, 271 as: m4+imem(@1)
         // Instruction Memory containing program defined by m4_asm(...) instantiations.
         //_@1
            /*SV_plus*/
               // The program in an instruction memory.
               logic [31:0] instrs [0:10-1];
               assign instrs = '{
                  {7'b0000000, 5'd0, 5'd0, 3'b000, 5'd10, 7'b0110011}, {7'b0000000, 5'd0, 5'd10, 3'b000, 5'd14, 7'b0110011}, {12'b1010, 5'd10, 3'b000, 5'd12, 7'b0010011}, {7'b0000000, 5'd0, 5'd10, 3'b000, 5'd13, 7'b0110011}, {7'b0000000, 5'd14, 5'd13, 3'b000, 5'd14, 7'b0110011}, {12'b1, 5'd13, 3'b000, 5'd13, 7'b0010011}, {1'b1, 6'b111111, 5'd12, 5'd13, 3'b100, 4'b1100, 1'b1, 7'b1100011}, {7'b0000000, 5'd0, 5'd14, 3'b000, 5'd10, 7'b0110011}, {7'b0000000, 5'd10, 5'd0, 3'b010, 5'b00100, 7'b0100011}, {12'b100, 5'd0, 3'b010, 5'd17, 7'b0000011}
               };
            for (imem = 0; imem <= 9; imem++) begin : L1_CPU_Imem //_/imem
               assign CPU_Imem_instr_a1[imem][31:0] = instrs[imem]; end
            //_?$imem_rd_en
               assign CPU_imem_rd_data_a1[31:0] = CPU_Imem_instr_a1[CPU_imem_rd_addr_a1];
          
      //_\end_source    // Args: (read stage)
      `line 272 "top.tlv" 2
      `line 34 "/raw.githubusercontent.com/stevehoover/RISCVMYTHWorkshop/c1719d5b338896577b79ee76c2f443ca2a76e14f/tlvlib/riscvshelllib.tlv" 1   // Instantiated from top.tlv, 272 as: m4+rf(@2, @3)
         // Reg File
         //_@3
            for (xreg = 0; xreg <= 31; xreg++) begin : L1_CPU_Xreg logic L1_wr_a3, L1_wr_a4; //_/xreg
               assign L1_wr_a3 = CPU_rf_wr_en_a3 && (CPU_rf_wr_index_a3 != 5'b0) && (CPU_rf_wr_index_a3 == xreg);
               assign CPU_Xreg_value_a3[xreg][31:0] = CPU_reset_a3 ?   xreg           :
                              L1_wr_a3        ?   CPU_rf_wr_data_a3 :
                                             CPU_Xreg_value_a4[xreg][31:0]; end
         //_@2
            //_?$rf_rd_en1
               assign CPU_rf_rd_data1_a2[31:0] = CPU_Xreg_value_a4[CPU_rf_rd_index1_a2];
            //_?$rf_rd_en2
               assign CPU_rf_rd_data2_a2[31:0] = CPU_Xreg_value_a4[CPU_rf_rd_index2_a2];
            `BOGUS_USE(CPU_rf_rd_data1_a2 CPU_rf_rd_data2_a2) 
      //_\end_source  // Args: (read stage, write stage) - if equal, no register bypass is required
      `line 273 "top.tlv" 2
      `line 51 "/raw.githubusercontent.com/stevehoover/RISCVMYTHWorkshop/c1719d5b338896577b79ee76c2f443ca2a76e14f/tlvlib/riscvshelllib.tlv" 1   // Instantiated from top.tlv, 273 as: m4+dmem(@4)
         // Data Memory
         //_@4
            for (dmem = 0; dmem <= 15; dmem++) begin : L1_CPU_Dmem logic L1_wr_a4; //_/dmem
               assign L1_wr_a4 = CPU_dmem_wr_en_a4 && (CPU_dmem_addr_a4 == dmem);
               assign CPU_Dmem_value_a4[dmem][31:0] = CPU_reset_a4 ?   dmem :
                              L1_wr_a4        ?   CPU_dmem_wr_data_a4 :
                                             CPU_Dmem_value_a5[dmem][31:0]; end
                                        
            //_?$dmem_rd_en
               assign CPU_dmem_rd_data_a4[31:0] = CPU_Dmem_value_a5[CPU_dmem_addr_a4];
            `BOGUS_USE(CPU_dmem_rd_data_a4)
      //_\end_source    // Args: (read/write stage)
      `line 274 "top.tlv" 2
   
   `line 64 "/raw.githubusercontent.com/stevehoover/RISCVMYTHWorkshop/c1719d5b338896577b79ee76c2f443ca2a76e14f/tlvlib/riscvshelllib.tlv" 1   // Instantiated from top.tlv, 275 as: m4+cpu_viz(@4)
      
      //_|cpu
         // for pulling default viz signals into CPU
         // and then back into viz
         //_@0
            assign {CPU_dummy_a0[0:0], CPU_is_csrrc_a0, CPU_is_csrrci_a0, CPU_is_csrrs_a0, CPU_is_csrrsi_a0, CPU_is_csrrw_a0, CPU_is_csrrwi_a0, CPU_is_store_a0} = {CPUVIZ_Defaults_dummy_a0, CPUVIZ_Defaults_is_csrrc_a0, CPUVIZ_Defaults_is_csrrci_a0, CPUVIZ_Defaults_is_csrrs_a0, CPUVIZ_Defaults_is_csrrsi_a0, CPUVIZ_Defaults_is_csrrw_a0, CPUVIZ_Defaults_is_csrrwi_a0, CPUVIZ_Defaults_is_store_a0};
            `BOGUS_USE(CPU_dummy_a0)
            for (xreg = 0; xreg <= 31; xreg++) begin : L1b_CPU_Xreg logic [0:0] L1_dummy_a0, L1_dummy_a1, L1_dummy_a2, L1_dummy_a3, L1_dummy_a4; //_/xreg
               assign {L1_dummy_a0[0:0]} = {L1_CPUVIZ_Defaults_Xreg[xreg].L1_dummy_a0}; end
            for (dmem = 0; dmem <= 15; dmem++) begin : L1b_CPU_Dmem logic [0:0] L1_dummy_a0, L1_dummy_a1, L1_dummy_a2, L1_dummy_a3, L1_dummy_a4; //_/dmem
               assign {L1_dummy_a0[0:0]} = {L1_CPUVIZ_Defaults_Dmem[dmem].L1_dummy_a0}; end
      // String representations of the instructions for debug.
      /*SV_plus*/
         logic [40*8-1:0] instr_strs [0:10];
         assign instr_strs = '{ "(R) ADD r10,r0,r0                       ",  "(R) ADD r14,r10,r0                      ",  "(I) ADDI r12,r10,1010                   ",  "(R) ADD r13,r10,r0                      ",  "(R) ADD r14,r13,r14                     ",  "(I) ADDI r13,r13,1                      ",  "(B) BLT r13,r12,1111111111000           ",  "(R) ADD r10,r14,r0                      ",  "(S) SW r0,r10,100                       ",  "(I) LW r17,r0,100                       ",  "END                                     "};
      //_|cpuviz
         //_@1
            for (imem = 0; imem <= 9; imem++) begin : L1_CPUVIZ_Imem logic [31:0] L1_instr_a1; logic [40*8-1:0] L1_instr_str_a1; //_/imem  // TODO: Cleanly report non-integer ranges.
               assign L1_instr_a1[31:0] = CPU_Imem_instr_a1[imem];
               assign L1_instr_str_a1[40*8-1:0] = instr_strs[imem];
               /* Viz omitted here */















               end
   
   
         //_@0
            //_/defaults
               assign {CPUVIZ_Defaults_is_lui_a0, CPUVIZ_Defaults_is_auipc_a0, CPUVIZ_Defaults_is_jal_a0, CPUVIZ_Defaults_is_jalr_a0, CPUVIZ_Defaults_is_beq_a0, CPUVIZ_Defaults_is_bne_a0, CPUVIZ_Defaults_is_blt_a0, CPUVIZ_Defaults_is_bge_a0, CPUVIZ_Defaults_is_bltu_a0, CPUVIZ_Defaults_is_bgeu_a0, CPUVIZ_Defaults_is_lb_a0, CPUVIZ_Defaults_is_lh_a0, CPUVIZ_Defaults_is_lw_a0, CPUVIZ_Defaults_is_lbu_a0, CPUVIZ_Defaults_is_lhu_a0, CPUVIZ_Defaults_is_sb_a0, CPUVIZ_Defaults_is_sh_a0, CPUVIZ_Defaults_is_sw_a0} = '0;
               assign {CPUVIZ_Defaults_is_addi_a0, CPUVIZ_Defaults_is_slti_a0, CPUVIZ_Defaults_is_sltiu_a0, CPUVIZ_Defaults_is_xori_a0, CPUVIZ_Defaults_is_ori_a0, CPUVIZ_Defaults_is_andi_a0, CPUVIZ_Defaults_is_slli_a0, CPUVIZ_Defaults_is_srli_a0, CPUVIZ_Defaults_is_srai_a0, CPUVIZ_Defaults_is_add_a0, CPUVIZ_Defaults_is_sub_a0, CPUVIZ_Defaults_is_sll_a0, CPUVIZ_Defaults_is_slt_a0, CPUVIZ_Defaults_is_sltu_a0, CPUVIZ_Defaults_is_xor_a0} = '0;
               assign {CPUVIZ_Defaults_is_srl_a0, CPUVIZ_Defaults_is_sra_a0, CPUVIZ_Defaults_is_or_a0, CPUVIZ_Defaults_is_and_a0, CPUVIZ_Defaults_is_csrrw_a0, CPUVIZ_Defaults_is_csrrs_a0, CPUVIZ_Defaults_is_csrrc_a0, CPUVIZ_Defaults_is_csrrwi_a0, CPUVIZ_Defaults_is_csrrsi_a0, CPUVIZ_Defaults_is_csrrci_a0} = '0;
               assign {CPUVIZ_Defaults_is_load_a0, CPUVIZ_Defaults_is_store_a0} = '0;
   
               assign CPUVIZ_Defaults_valid_a0               = 1'b1;
               assign CPUVIZ_Defaults_rd_a0[4:0]             = 5'b0;
               assign CPUVIZ_Defaults_rs1_a0[4:0]            = 5'b0;
               assign CPUVIZ_Defaults_rs2_a0[4:0]            = 5'b0;
               assign CPUVIZ_Defaults_src1_value_a0[31:0]    = 32'b0;
               assign CPUVIZ_Defaults_src2_value_a0[31:0]    = 32'b0;
   
               assign CPUVIZ_Defaults_result_a0[31:0]        = 32'b0;
               assign CPUVIZ_Defaults_pc_a0[31:0]            = 32'b0;
               assign CPUVIZ_Defaults_imm_a0[31:0]           = 32'b0;
   
               assign CPUVIZ_Defaults_is_s_instr_a0          = 1'b0;
   
               assign CPUVIZ_Defaults_rd_valid_a0            = 1'b0;
               assign CPUVIZ_Defaults_rs1_valid_a0           = 1'b0;
               assign CPUVIZ_Defaults_rs2_valid_a0           = 1'b0;
               assign CPUVIZ_Defaults_rf_wr_en_a0            = 1'b0;
               assign CPUVIZ_Defaults_rf_wr_index_a0[4:0]    = 5'b0;
               assign CPUVIZ_Defaults_rf_wr_data_a0[31:0]    = 32'b0;
               assign CPUVIZ_Defaults_rf_rd_en1_a0           = 1'b0;
               assign CPUVIZ_Defaults_rf_rd_en2_a0           = 1'b0;
               assign CPUVIZ_Defaults_rf_rd_index1_a0[4:0]   = 5'b0;
               assign CPUVIZ_Defaults_rf_rd_index2_a0[4:0]   = 5'b0;
   
               assign CPUVIZ_Defaults_ld_data_a0[31:0]       = 32'b0;
               assign CPUVIZ_Defaults_imem_rd_en_a0          = 1'b0;
               assign CPUVIZ_Defaults_imem_rd_addr_a0[4-1:0] = {4{1'b0}};
               
               for (xreg = 0; xreg <= 31; xreg++) begin : L1_CPUVIZ_Defaults_Xreg logic [0:0] L1_dummy_a0; logic [31:0] L1_value_a0; logic L1_wr_a0; //_/xreg
                  assign L1_value_a0[31:0]      = 32'b0;
                  assign L1_wr_a0               = 1'b0;
                  `BOGUS_USE(L1_value_a0 L1_wr_a0)
                  assign L1_dummy_a0[0:0]       = 1'b0; end
               for (dmem = 0; dmem <= 15; dmem++) begin : L1_CPUVIZ_Defaults_Dmem logic [0:0] L1_dummy_a0; logic [31:0] L1_value_a0; logic L1_wr_a0; //_/dmem
                  assign L1_value_a0[31:0]      = 32'0;
                  assign L1_wr_a0               = 1'b0;
                  `BOGUS_USE(L1_value_a0 L1_wr_a0) 
                  assign L1_dummy_a0[0:0]       = 1'b0; end
               `BOGUS_USE(CPUVIZ_Defaults_is_lui_a0 CPUVIZ_Defaults_is_auipc_a0 CPUVIZ_Defaults_is_jal_a0 CPUVIZ_Defaults_is_jalr_a0 CPUVIZ_Defaults_is_beq_a0 CPUVIZ_Defaults_is_bne_a0 CPUVIZ_Defaults_is_blt_a0 CPUVIZ_Defaults_is_bge_a0 CPUVIZ_Defaults_is_bltu_a0 CPUVIZ_Defaults_is_bgeu_a0 CPUVIZ_Defaults_is_lb_a0 CPUVIZ_Defaults_is_lh_a0 CPUVIZ_Defaults_is_lw_a0 CPUVIZ_Defaults_is_lbu_a0 CPUVIZ_Defaults_is_lhu_a0 CPUVIZ_Defaults_is_sb_a0 CPUVIZ_Defaults_is_sh_a0 CPUVIZ_Defaults_is_sw_a0)
               `BOGUS_USE(CPUVIZ_Defaults_is_addi_a0 CPUVIZ_Defaults_is_slti_a0 CPUVIZ_Defaults_is_sltiu_a0 CPUVIZ_Defaults_is_xori_a0 CPUVIZ_Defaults_is_ori_a0 CPUVIZ_Defaults_is_andi_a0 CPUVIZ_Defaults_is_slli_a0 CPUVIZ_Defaults_is_srli_a0 CPUVIZ_Defaults_is_srai_a0 CPUVIZ_Defaults_is_add_a0 CPUVIZ_Defaults_is_sub_a0 CPUVIZ_Defaults_is_sll_a0 CPUVIZ_Defaults_is_slt_a0 CPUVIZ_Defaults_is_sltu_a0 CPUVIZ_Defaults_is_xor_a0)
               `BOGUS_USE(CPUVIZ_Defaults_is_srl_a0 CPUVIZ_Defaults_is_sra_a0 CPUVIZ_Defaults_is_or_a0 CPUVIZ_Defaults_is_and_a0 CPUVIZ_Defaults_is_csrrw_a0 CPUVIZ_Defaults_is_csrrs_a0 CPUVIZ_Defaults_is_csrrc_a0 CPUVIZ_Defaults_is_csrrwi_a0 CPUVIZ_Defaults_is_csrrsi_a0 CPUVIZ_Defaults_is_csrrci_a0)
               `BOGUS_USE(CPUVIZ_Defaults_is_load_a0 CPUVIZ_Defaults_is_store_a0)
               `BOGUS_USE(CPUVIZ_Defaults_valid_a0 CPUVIZ_Defaults_rd_a0 CPUVIZ_Defaults_rs1_a0 CPUVIZ_Defaults_rs2_a0 CPUVIZ_Defaults_src1_value_a0 CPUVIZ_Defaults_src2_value_a0 CPUVIZ_Defaults_result_a0 CPUVIZ_Defaults_pc_a0 CPUVIZ_Defaults_imm_a0)
               `BOGUS_USE(CPUVIZ_Defaults_is_s_instr_a0 CPUVIZ_Defaults_rd_valid_a0 CPUVIZ_Defaults_rs1_valid_a0 CPUVIZ_Defaults_rs2_valid_a0)
               `BOGUS_USE(CPUVIZ_Defaults_rf_wr_en_a0 CPUVIZ_Defaults_rf_wr_index_a0 CPUVIZ_Defaults_rf_wr_data_a0 CPUVIZ_Defaults_rf_rd_en1_a0 CPUVIZ_Defaults_rf_rd_en2_a0 CPUVIZ_Defaults_rf_rd_index1_a0 CPUVIZ_Defaults_rf_rd_index2_a0 CPUVIZ_Defaults_ld_data_a0)
               `BOGUS_USE(CPUVIZ_Defaults_imem_rd_en_a0 CPUVIZ_Defaults_imem_rd_addr_a0)
               
               assign CPUVIZ_Defaults_dummy_a0[0:0]          = 1'b0;
         //_@4
            assign {CPUVIZ_imm_a4[31:0], CPUVIZ_is_add_a4, CPUVIZ_is_addi_a4, CPUVIZ_is_and_a4, CPUVIZ_is_andi_a4, CPUVIZ_is_auipc_a4, CPUVIZ_is_beq_a4, CPUVIZ_is_bge_a4, CPUVIZ_is_bgeu_a4, CPUVIZ_is_blt_a4, CPUVIZ_is_bltu_a4, CPUVIZ_is_bne_a4, CPUVIZ_is_csrrc_a4, CPUVIZ_is_csrrci_a4, CPUVIZ_is_csrrs_a4, CPUVIZ_is_csrrsi_a4, CPUVIZ_is_csrrw_a4, CPUVIZ_is_csrrwi_a4, CPUVIZ_is_jal_a4, CPUVIZ_is_jalr_a4, CPUVIZ_is_lb_a4, CPUVIZ_is_lbu_a4, CPUVIZ_is_lh_a4, CPUVIZ_is_lhu_a4, CPUVIZ_is_load_a4, CPUVIZ_is_lui_a4, CPUVIZ_is_lw_a4, CPUVIZ_is_or_a4, CPUVIZ_is_ori_a4, CPUVIZ_is_sb_a4, CPUVIZ_is_sh_a4, CPUVIZ_is_sll_a4, CPUVIZ_is_slli_a4, CPUVIZ_is_slt_a4, CPUVIZ_is_slti_a4, CPUVIZ_is_sltiu_a4, CPUVIZ_is_sltu_a4, CPUVIZ_is_sra_a4, CPUVIZ_is_srai_a4, CPUVIZ_is_srl_a4, CPUVIZ_is_srli_a4, CPUVIZ_is_store_a4, CPUVIZ_is_sub_a4, CPUVIZ_is_sw_a4, CPUVIZ_is_xor_a4, CPUVIZ_is_xori_a4, CPUVIZ_pc_a4[31:0], CPUVIZ_rd_a4[4:0], CPUVIZ_rd_valid_a4, CPUVIZ_result_a4[31:0], CPUVIZ_rs1_a4[4:0], CPUVIZ_rs1_valid_a4, CPUVIZ_rs2_a4[4:0], CPUVIZ_rs2_valid_a4, CPUVIZ_src1_value_a4[31:0], CPUVIZ_src2_value_a4[31:0], CPUVIZ_valid_a4} = {CPU_imm_a4, CPU_is_add_a4, CPU_is_addi_a4, CPU_is_and_a4, CPU_is_andi_a4, CPU_is_auipc_a4, CPU_is_beq_a4, CPU_is_bge_a4, CPU_is_bgeu_a4, CPU_is_blt_a4, CPU_is_bltu_a4, CPU_is_bne_a4, CPU_is_csrrc_a4, CPU_is_csrrci_a4, CPU_is_csrrs_a4, CPU_is_csrrsi_a4, CPU_is_csrrw_a4, CPU_is_csrrwi_a4, CPU_is_jal_a4, CPU_is_jalr_a4, CPU_is_lb_a4, CPU_is_lbu_a4, CPU_is_lh_a4, CPU_is_lhu_a4, CPU_is_load_a4, CPU_is_lui_a4, CPU_is_lw_a4, CPU_is_or_a4, CPU_is_ori_a4, CPU_is_sb_a4, CPU_is_sh_a4, CPU_is_sll_a4, CPU_is_slli_a4, CPU_is_slt_a4, CPU_is_slti_a4, CPU_is_sltiu_a4, CPU_is_sltu_a4, CPU_is_sra_a4, CPU_is_srai_a4, CPU_is_srl_a4, CPU_is_srli_a4, CPU_is_store_a4, CPU_is_sub_a4, CPU_is_sw_a4, CPU_is_xor_a4, CPU_is_xori_a4, CPU_pc_a4, CPU_rd_a4, CPU_rd_valid_a4, CPU_result_a4, CPU_rs1_a4, CPU_rs1_valid_a4, CPU_rs2_a4, CPU_rs2_valid_a4, CPU_src1_value_a4, CPU_src2_value_a4, CPU_valid_a4};
            
            for (xreg = 0; xreg <= 31; xreg++) begin : L1_CPUVIZ_Xreg logic [0:0] L1_dummy_a4; logic [31:0] L1_value_a4, L1_value_a5; logic L1_wr_a4; //_/xreg
               assign {L1_dummy_a4[0:0], L1_value_a4[31:0], L1_wr_a4} = {L1b_CPU_Xreg[xreg].L1_dummy_a4, CPU_Xreg_value_a4[xreg], L1_CPU_Xreg[xreg].L1_wr_a4};
               `BOGUS_USE(L1_dummy_a4) end
            
            for (dmem = 0; dmem <= 15; dmem++) begin : L1_CPUVIZ_Dmem logic [0:0] L1_dummy_a4; logic [31:0] L1_value_a4, L1_value_a5; logic L1_wr_a4; //_/dmem
               assign {L1_dummy_a4[0:0], L1_value_a4[31:0], L1_wr_a4} = {L1b_CPU_Dmem[dmem].L1_dummy_a4, CPU_Dmem_value_a4[dmem], L1_CPU_Dmem[dmem].L1_wr_a4};
               `BOGUS_USE(L1_dummy_a4) end
   
            // m4_mnemonic_expr is build for WARP-V signal names, which are slightly different. Correct them.
            
            assign CPUVIZ_mnemonic_a4[10*8-1:0] = CPUVIZ_is_lui_a4 ? "LUI       " : CPUVIZ_is_auipc_a4 ? "AUIPC     " : CPUVIZ_is_jal_a4 ? "JAL       " : CPUVIZ_is_jalr_a4 ? "JALR      " : CPUVIZ_is_beq_a4 ? "BEQ       " : CPUVIZ_is_bne_a4 ? "BNE       " : CPUVIZ_is_blt_a4 ? "BLT       " : CPUVIZ_is_bge_a4 ? "BGE       " : CPUVIZ_is_bltu_a4 ? "BLTU      " : CPUVIZ_is_bgeu_a4 ? "BGEU      " : CPUVIZ_is_lb_a4 ? "LB        " : CPUVIZ_is_lh_a4 ? "LH        " : CPUVIZ_is_lw_a4 ? "LW        " : CPUVIZ_is_lbu_a4 ? "LBU       " : CPUVIZ_is_lhu_a4 ? "LHU       " : CPUVIZ_is_sb_a4 ? "SB        " : CPUVIZ_is_sh_a4 ? "SH        " : CPUVIZ_is_sw_a4 ? "SW        " : CPUVIZ_is_addi_a4 ? "ADDI      " : CPUVIZ_is_slti_a4 ? "SLTI      " : CPUVIZ_is_sltiu_a4 ? "SLTIU     " : CPUVIZ_is_xori_a4 ? "XORI      " : CPUVIZ_is_ori_a4 ? "ORI       " : CPUVIZ_is_andi_a4 ? "ANDI      " : CPUVIZ_is_slli_a4 ? "SLLI      " : CPUVIZ_is_srli_a4 ? "SRLI      " : CPUVIZ_is_srai_a4 ? "SRAI      " : CPUVIZ_is_add_a4 ? "ADD       " : CPUVIZ_is_sub_a4 ? "SUB       " : CPUVIZ_is_sll_a4 ? "SLL       " : CPUVIZ_is_slt_a4 ? "SLT       " : CPUVIZ_is_sltu_a4 ? "SLTU      " : CPUVIZ_is_xor_a4 ? "XOR       " : CPUVIZ_is_srl_a4 ? "SRL       " : CPUVIZ_is_sra_a4 ? "SRA       " : CPUVIZ_is_or_a4 ? "OR        " : CPUVIZ_is_and_a4 ? "AND       " : CPUVIZ_is_csrrw_a4 ? "CSRRW     " : CPUVIZ_is_csrrs_a4 ? "CSRRS     " : CPUVIZ_is_csrrc_a4 ? "CSRRC     " : CPUVIZ_is_csrrwi_a4 ? "CSRRWI    " : CPUVIZ_is_csrrsi_a4 ? "CSRRSI    " : CPUVIZ_is_csrrci_a4 ? "CSRRCI    " :  CPUVIZ_is_load_a4 ? "LOAD      " : CPUVIZ_is_store_a4 ? "STORE     " : "ILLEGAL   ";
            /* Viz omitted here */



















































            //
            // Register file
            //
            for (xreg = 0; xreg <= 31; xreg++) begin : L1b_CPUVIZ_Xreg //_/xreg           
               /* Viz omitted here */
























               end
            //
            // DMem
            //
            for (dmem = 0; dmem <= 15; dmem++) begin : L1b_CPUVIZ_Dmem //_/dmem
               /* Viz omitted here */
























               end
      
   //_\end_source    // For visualisation, argument should be at least equal to the last stage of CPU logic
   `line 276 "top.tlv" 2
                       // @4 would work for all labs
//_\SV
   endmodule


// Undefine macros defined by SandPiper (in "top_gen.sv").
`undef BOGUS_USE