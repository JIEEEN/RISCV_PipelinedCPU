//
//  Author: Prof. Taeweon Suh
//          Computer Science & Engineering
//          Korea University
//  Date: July 14, 2020
//  Description: Skeleton design of RV32I Single-cycle CPU
//

`timescale 1ns/1ns
`define simdelay 1

module rv32i_cpu (
		      input         clk, reset,
            output [31:0] pc,		  		// program counter for instruction fetch
            input  [31:0] inst, 			// incoming instruction
            output        Memwrite, 	// 'memory write' control signal
            output [31:0] Memaddr,  	// memory address 
            output [31:0] MemWdata, 	// data to write to memory
            input  [31:0] MemRdata); 	// data read from memory

  // ###### SangJin Park : Start #####
  wire        auipc, lui;
  wire        alusrc, regwrite;
  wire [4:0]  alucontrol;
  wire        memtoreg, memwrite;
  wire        branch, jal, jalr, stall;
  
  reg	 [31:0] inst_IF_ID;

  always @(posedge clk) 	//instruction flip-flop
	begin
		if(stall)
			inst_IF_ID <= inst_IF_ID;
		else inst_IF_ID <= inst;
	end

  // ###### SangJin Park : End #####

  // Instantiate Controller
  controller i_controller(
  		// ###### SangJin Park : Start #####
      	.opcode		(inst_IF_ID[6:0]), 
		.funct7		(inst_IF_ID[31:25]), 
		.funct3		(inst_IF_ID[14:12]), 
		// ###### SangJin Park : End #####
		.auipc		(auipc),
		.lui			(lui),
		.memtoreg	(memtoreg),
		.memwrite	(memwrite),
		.branch		(branch),
		.alusrc		(alusrc),
		.regwrite	(regwrite),
		.jal			(jal),
		.jalr			(jalr),
		.alucontrol	(alucontrol));

  // Instantiate Datapath
  datapath i_datapath(
		.clk				(clk),
		.reset			(reset),
		.auipc			(auipc),
		.lui				(lui),
		.memtoreg		(memtoreg),
		.memwrite		(memwrite),
		.branch			(branch),
		.alusrc			(alusrc),
		.regwrite		(regwrite),
		.jal				(jal),
		.jalr				(jalr),
		.alucontrol		(alucontrol),
		.pc				(pc),
  		// ###### SangJin Park : Start #####
		.inst				(inst_IF_ID),
		.aluout_EXE_MEM			(Memaddr), 
		.MemWdata_EXE_MEM		(MemWdata),
		.MemRdata_EXE_MEM		(MemRdata),
		.memwrite_tmp		(Memwrite),
		.stall_tmp			(stall));
		// ###### SangJin Park : End #####

endmodule


//
// Instruction Decoder 
// to generate control signals for datapath
//
module controller(input  [6:0] opcode,
                  input  [6:0] funct7,
                  input  [2:0] funct3,
                  output       auipc,
                  output       lui,
                  output       alusrc,
                  output [4:0] alucontrol,
                  output       branch,
                  output       jal,
                  output       jalr,
                  output       memtoreg,
                  output       memwrite,
                  output       regwrite);

	maindec i_maindec(
		.opcode		(opcode),
		.auipc		(auipc),
		.lui			(lui),
		.memtoreg	(memtoreg),
		.memwrite	(memwrite),
		.branch		(branch),
		.alusrc		(alusrc),
		.regwrite	(regwrite),
		.jal			(jal),
		.jalr			(jalr));

	aludec i_aludec( 
		.opcode     (opcode),
		.funct7     (funct7),
		.funct3     (funct3),
		.alucontrol (alucontrol));


endmodule


//
// RV32I Opcode map = Inst[6:0]
//
`define OP_R			7'b0110011
`define OP_I_ARITH	7'b0010011
`define OP_I_LOAD  	7'b0000011
`define OP_I_JALR  	7'b1100111		
`define OP_S			7'b0100011
`define OP_B			7'b1100011
`define OP_U_LUI		7'b0110111
`define OP_U_AUIPC	7'b0010111
`define OP_J_JAL		7'b1101111

//
// Main decoder generates all control signals except alucontrol 
//
//
module maindec(input  [6:0] opcode,
               output       auipc,
               output       lui,
               output       regwrite,
               output       alusrc,
               output       memtoreg, memwrite,
               output       branch, 
               output       jal,
               output       jalr);

  reg [8:0] controls;

  assign {auipc, lui, regwrite, alusrc, 
			 memtoreg, memwrite, branch, jal, 
			 jalr} = controls;

  always @(*)
  begin
    case(opcode)
      `OP_R: 			controls <= #`simdelay 9'b0010_0000_0; // R-type
      `OP_I_ARITH: 	controls <= #`simdelay 9'b0011_0000_0; // I-type Arithmetic
      `OP_I_LOAD: 	controls <= #`simdelay 9'b0011_1000_0; // I-type Load
      `OP_I_JALR: 	controls <= #`simdelay 9'b0011_0000_1; // JALR
      `OP_S: 			controls <= #`simdelay 9'b0001_0100_0; // S-type Store
      `OP_B: 			controls <= #`simdelay 9'b0000_0010_0; // B-type Branch
      `OP_U_LUI: 		controls <= #`simdelay 9'b0111_0000_0; // LUI
		`OP_U_AUIPC:	controls <= #`simdelay 9'b1010_0000_0; // AUIPC
      `OP_J_JAL: 		controls <= #`simdelay 9'b0011_0001_0; // JAL
      default:    	controls <= #`simdelay 9'b0000_0000_0; // ???
    endcase
  end

endmodule

//
// ALU decoder generates ALU control signal (alucontrol)
//
module aludec(input      [6:0] opcode,
              input      [6:0] funct7,
              input      [2:0] funct3,
              output reg [4:0] alucontrol);

  always @(*)

    case(opcode)

      `OP_R:   		// R-type
		begin
			case({funct7,funct3})
			 10'b0000000_000: alucontrol <= #`simdelay 5'b00000; // addition (add)
			 10'b0100000_000: alucontrol <= #`simdelay 5'b10000; // subtraction (sub)
			 10'b0000000_111: alucontrol <= #`simdelay 5'b00001; // and (and)
			 10'b0000000_110: alucontrol <= #`simdelay 5'b00010; // or (or)
			 10'b0000000_100: alucontrol <= #`simdelay 5'b00011; // xor 
			 10'b0000000_001: alucontrol <= #`simdelay 5'b00100; // sll
          default:         alucontrol <= #`simdelay 5'bxxxxx; // ???
        endcase
		end

      `OP_I_ARITH:   // I-type Arithmetic
		begin
			casez({funct7, funct3})
			 10'b???????_000:  alucontrol <= #`simdelay 5'b00000; // additioni
			 10'b???????_110:  alucontrol <= #`simdelay 5'b00010; // ori	
			 10'b???????_111:  alucontrol <= #`simdelay 5'b00001; // andi
			 10'b???????_100:  alucontrol <= #`simdelay 5'b00011; // xori
			 10'b0000000_001:  alucontrol <= #`simdelay 5'b00100; // slli
          default: alucontrol <= #`simdelay 5'bxxxxx; // ???
        endcase
		end

      `OP_I_LOAD: 	// I-type Load (LW, LH, LB...)
			alucontrol <= #`simdelay 5'b00000;	// addition 
      `OP_I_JALR: 	// I-type (JALR)
			alucontrol <= #`simdelay 5'b00000;	// addition 
      `OP_S:  		// S-type Store (SW, SH, SB)
			alucontrol <= #`simdelay 5'b00000;	// addition 
      `OP_U_LUI: 		// U-type (LUI)
			alucontrol <= #`simdelay 5'b00000;	// addition 
      `OP_U_AUIPC: 	// U-type (AUIPC)
      	alucontrol <= #`simdelay 5'b00000;  // addition 

      `OP_B:   		// B-type Branch (BEQ, BNE, ...)
      	alucontrol <= #`simdelay 5'b10000;  // subtraction 

      default: 
      	alucontrol <= #`simdelay 5'b00000;  //

    endcase
    
endmodule


//
// CPU datapath
//
module datapath(input         clk, reset,
                input  [31:0] inst,
                input         auipc,
                input         lui,
                input         regwrite,
                input         memtoreg,
                input         memwrite,
                input         alusrc, 
                input  [4:0]  alucontrol,
                input         branch,
                input         jal,
                input         jalr,

                output reg [31:0] pc,
				
  				// ###### SangJin Park : Start #####
				output reg memwrite_tmp,
				output reg stall_tmp,
                output reg [31:0] aluout_EXE_MEM,
                output reg [31:0] MemWdata_EXE_MEM,
                input  [31:0] MemRdata_EXE_MEM);
  				// ###### SangJin Park : End #####

  wire [4:0]  rs1, rs2, rd;
  wire [2:0]  funct3;
  wire [31:0] rs1_data, rs2_data;
  reg  [31:0] rd_data;
  wire [20:1] jal_imm;
  wire [31:0] se_jal_imm;
  wire [12:1] br_imm;
  wire [31:0] se_br_imm;
  reg [31:0] se_imm_itype;
  reg [31:0] se_imm_stype;
  reg [31:0] auipc_lui_imm;
  reg  [31:0] alusrc1;
  reg  [31:0] alusrc2;
  wire [31:0] branch_dest, jal_dest, jalr_dest;	
  wire		  Nflag, Zflag, Cflag, Vflag;
  wire		  f3beq, f3blt, f3bgeu;
  wire		  beq_taken;
  wire		  blt_taken;
  wire		  bgeu_taken;		
  wire		  btaken;

  
  // ###### SangJin Park : Start #####
  //var added for Flip-Flop
  wire [31:0] aluout_ID_EXE;
  
  reg  [31:0] rs1_data_tmp, rs2_data_tmp;
  reg  [31:0] aluout_MEM_WB;
  reg  [31:0] MemWdata_ID_EXE, MemRdata_MEM_WB;
  reg  [31:0] rs1_ID_EXE, rs2_ID_EXE;
  reg  [31:0] pc_IF_ID, pc_ID_EXE, pc_EXE_MEM, pc_MEM_WB;
  reg  [31:0] rs1_data_ID_EXE, rs2_data_ID_EXE;
  reg  [4:0]  rd_ID_EXE, rd_EXE_MEM, rd_MEM_WB;
  reg  [4:0]  alucontrol_ID_EXE;
  reg  		  alusrc_ID_EXE, branch_ID_EXE, branch_EXE_MEM;
  reg	      memwrite_ID_EXE, memwrite_EXE_MEM;
  reg		  memtoreg_ID_EXE, memtoreg_EXE_MEM, memtoreg_MEM_WB;
  reg		  regwrite_ID_EXE, regwrite_EXE_MEM, regwrite_MEM_WB;
  reg		  auipc_ID_EXE, lui_ID_EXE;
  reg   	  jal_ID_EXE, jal_EXE_MEM, jal_MEM_WB;
  reg		  jalr_ID_EXE, jalr_EXE_MEM, jalr_MEM_WB;
  
  reg  [31:0] auipc_lui_imm_ID_EXE, se_imm_itype_ID_EXE, se_imm_stype_ID_EXE;
  
  reg [1:0]  fw1, fw2;
  wire [1:0] fw1_tmp, fw2_tmp;		

  // ###### SangJin Park : End #####
  
  // ###### SangJin Park : Start #####
  always @(*)
	begin
		fw1 <= fw1_tmp;
		fw2 <= fw2_tmp;
	end
  // ###### SangJin Park : End #####

  
  assign rs1 = inst[19:15];
  assign rs2 = inst[24:20];
  assign rd  = inst[11:7];
  assign funct3  = inst[14:12];

  //
  // PC (Program Counter) logic 
  //
  assign f3beq  = (funct3 == 3'b000);
  assign f3blt  = (funct3 == 3'b100);
  assign f3bgeu = (funct3 == 3'b111);

  assign beq_taken  =  branch & f3beq & Zflag;
  assign blt_taken  =  branch & f3blt & (Nflag != Vflag);
  assign bgeu_taken =  branch & f3bgeu & Cflag;	
  assign btaken     =  beq_taken  | blt_taken | bgeu_taken; 

  // ###### SangJin Park : Start #####
  assign branch_dest = (pc_IF_ID + se_br_imm);
  assign jal_dest 	= (pc_IF_ID + se_jal_imm);
  assign jalr_dest   = {aluout_EXE_MEM[31:0]};
  // ###### SangJin Park : End #####

  always @(posedge clk, posedge reset)
  begin
     if (reset)  pc <= 32'b0;
	  else 
  		// ###### SangJin Park : Start ##### 
	  begin
	      if (btaken) // branch_taken
				pc <= #`simdelay branch_dest;
		   else if (jal) // jal
				pc <= #`simdelay jal_dest;
			else if (jalr)
				pc <= #`simdelay jalr_dest;	
		   else if (stall_tmp)
				pc <= pc;
			else	
				pc <= #`simdelay (pc + 4);
	  end
  		// ###### SangJin Park : End #####
  end


  // JAL immediate
  assign jal_imm[20:1] = {inst[31],inst[19:12],inst[20],inst[30:21]};
  assign se_jal_imm[31:0] = {{11{jal_imm[20]}},jal_imm[20:1],1'b0};

  // Branch immediate
  assign br_imm[12:1] = {inst[31],inst[7],inst[30:25],inst[11:8]};
  assign se_br_imm[31:0] = {{19{br_imm[12]}},br_imm[12:1],1'b0};



  // 
  // Register File 
  //
  regfile i_regfile(
    .clk	    (clk),
    .we			(regwrite_MEM_WB),
    .rs1		(rs1),
    .rs2		(rs2),
    .rd			(rd_MEM_WB),
    .rd_data	(rd_data),
    .rs1_data	(rs1_data),
    .rs2_data	(rs2_data));


	//assign MemWdata = rs2_data;
	
	
	
  	// ###### SangJin Park : Start ##### 
	//ff : IF -> ID
	always @(posedge clk)
		begin
			if(stall_tmp)
				pc_IF_ID <= pc_IF_ID;
			else
				pc_IF_ID <= pc;
		end
	
	
	//ff : ID -> EXE
	always @(posedge clk)
		if(stall_tmp)
			begin
				rs1_ID_EXE <= 0;
				rs2_ID_EXE <= 0;
				rd_ID_EXE <= 0;
				pc_ID_EXE <= 0;
				memwrite_ID_EXE <= 0;
				regwrite_ID_EXE <= 0;
				alusrc_ID_EXE <= 0;
				alucontrol_ID_EXE <= 0;
				memwrite_ID_EXE <= 0;
				memtoreg_ID_EXE <= 0;
				regwrite_ID_EXE <= 0;
				branch_ID_EXE <= 0;
				auipc_ID_EXE <= 0;
				lui_ID_EXE <= 0;
				jal_ID_EXE <= 0;
				jalr_ID_EXE <= 0;
			end
		else
			begin
				//control signal
				alusrc_ID_EXE <= alusrc;
				alucontrol_ID_EXE <= alucontrol;
				memwrite_ID_EXE <= memwrite;
				memtoreg_ID_EXE <= memtoreg;
				regwrite_ID_EXE <= regwrite;
				branch_ID_EXE <= branch;
				auipc_ID_EXE <= auipc;
				lui_ID_EXE <= lui;
				jal_ID_EXE <= jal;
				jalr_ID_EXE <= jalr;
				
				//data
				pc_ID_EXE <= pc_IF_ID;
				rs1_ID_EXE <= rs1;
				rs2_ID_EXE <= rs2;
				rd_ID_EXE <= rd;
				rs1_data_ID_EXE <= rs1_data_tmp;
				rs2_data_ID_EXE <= rs2_data_tmp;
				
				//imm
				auipc_lui_imm_ID_EXE <= auipc_lui_imm;
				se_imm_itype_ID_EXE <= se_imm_itype;
				se_imm_stype_ID_EXE <= se_imm_stype;
			end
		
	
	//ff : EXE -> MEM
	always @(posedge clk)
		begin
			//control
			memwrite_EXE_MEM <= memwrite_ID_EXE;
			memtoreg_EXE_MEM <= memtoreg_ID_EXE;
			regwrite_EXE_MEM <= regwrite_ID_EXE;
			branch_EXE_MEM <= branch_ID_EXE;
			jal_EXE_MEM <= jal_ID_EXE;
			jalr_EXE_MEM <= jalr_ID_EXE;
			
			aluout_EXE_MEM <= aluout_ID_EXE;
			pc_EXE_MEM <= pc_ID_EXE;
			rd_EXE_MEM <= rd_ID_EXE;
			MemWdata_EXE_MEM <= MemWdata_ID_EXE;
		end
	
	
	//ff : MEM -> WB
	always @(posedge clk)
		begin
			//control
			memtoreg_MEM_WB <= memtoreg_EXE_MEM;
			regwrite_MEM_WB <= regwrite_EXE_MEM;
			jal_MEM_WB <= jal_EXE_MEM;
			jalr_MEM_WB <= jalr_EXE_MEM;
			
			pc_MEM_WB <= pc_EXE_MEM;
			aluout_MEM_WB <= aluout_EXE_MEM;
			rd_MEM_WB <= rd_EXE_MEM;
			MemRdata_MEM_WB <= MemRdata_EXE_MEM;
		end
  	// ###### SangJin Park : End ##### 
	

	


  	// ###### SangJin Park : Start ##### 
	
	// interlock - switch stall
    always@(*)
    begin
      if(memtoreg_ID_EXE && ((rd_ID_EXE == rs1) || (rd_ID_EXE == rs2))) 
	  		stall_tmp = 1'b1;
      else  stall_tmp = 1'b0;
    end
	 
	 
    always@(*)
    begin
      if((rd_MEM_WB == rs2_ID_EXE) && memtoreg_MEM_WB && memwrite_ID_EXE) 
	  		MemWdata_ID_EXE = MemRdata_MEM_WB;
	   else if ((rd_MEM_WB == rs2_ID_EXE) && regwrite_MEM_WB && (~memtoreg_MEM_WB) && memwrite_ID_EXE) 
	   		MemWdata_ID_EXE = aluout_MEM_WB;
	   else MemWdata_ID_EXE = rs2_data_ID_EXE;
    end
      
    always@(*)
	 begin
      memwrite_tmp = memwrite_EXE_MEM;
		end

		
    always@(*)
    begin
     if ((rd_MEM_WB == rs1) && memtoreg_MEM_WB && (regwrite || memwrite)) 
	 	rs1_data_tmp = MemRdata_MEM_WB;
     else if ((rd_MEM_WB == rs1) && regwrite_MEM_WB && (regwrite || memwrite)) 
	 	rs1_data_tmp = rd_data;
     else rs1_data_tmp = rs1_data;
    end

    always@(*)
    begin
      if ((rd_MEM_WB == rs2) && memtoreg_MEM_WB && (regwrite || memwrite)) 
	  		rs2_data_tmp = MemRdata_MEM_WB;
      else if ((rd_MEM_WB == rs2) && regwrite_MEM_WB && (regwrite || memwrite)) 
	  		rs2_data_tmp = rd_data;
      else  rs2_data_tmp = rs2_data;
    end


    

  	// ###### SangJin Park : End ##### 





	//
	// ALU 
	//
	alu i_alu(
		.a			(alusrc1),
		.b			(alusrc2),
		.alucont	(alucontrol_ID_EXE),
		.result	(aluout_ID_EXE),
		.N			(Nflag),
		.Z			(Zflag),
		.C			(Cflag),
		.V			(Vflag));
		
    // ###### SangJin Park: Start #######

	// 1st source to ALU (alusrc1)
	always@(*)
	begin
		if      (auipc_ID_EXE)	alusrc1[31:0]  =  pc_ID_EXE;  
		else if (lui_ID_EXE) 		alusrc1[31:0]  =  32'b0;
    	else if ((rd_MEM_WB == rs1_ID_EXE) && memtoreg_MEM_WB && (regwrite_ID_EXE || memwrite_ID_EXE)) 
				alusrc1[31:0] = MemRdata_MEM_WB;
    	else if ((rd_EXE_MEM == rs1_ID_EXE) && regwrite_EXE_MEM && (regwrite_ID_EXE || memwrite_ID_EXE)) 
				alusrc1[31:0] = aluout_EXE_MEM;
    	else if ((rd_MEM_WB == rs1_ID_EXE) && regwrite_MEM_WB && (regwrite_ID_EXE || memwrite_ID_EXE))   
				alusrc1[31:0] = aluout_MEM_WB;
    	else    alusrc1[31:0] = rs1_data_ID_EXE[31:0];
	end
	
	// 2nd source to ALU (alusrc2)
	always@(*)
	begin
		if	     (auipc_ID_EXE | lui_ID_EXE)	    alusrc2[31:0] = auipc_lui_imm_ID_EXE[31:0];
		else if (alusrc_ID_EXE & memwrite_ID_EXE)	alusrc2[31:0] = se_imm_stype_ID_EXE[31:0];
		else if (alusrc_ID_EXE)		              alusrc2[31:0] = se_imm_itype_ID_EXE[31:0];
    	else if ((rd_MEM_WB == rs2_ID_EXE) && memtoreg_MEM_WB && regwrite_ID_EXE && ~alusrc_ID_EXE) 
				alusrc2[31:0] = MemRdata_MEM_WB; 
    	else if ((rd_EXE_MEM == rs2_ID_EXE) && regwrite_EXE_MEM && regwrite_ID_EXE  && ~alusrc_ID_EXE) 
				alusrc2[31:0] = aluout_EXE_MEM;     
    	else if ((rd_MEM_WB == rs2_ID_EXE) && regwrite_MEM_WB && regwrite_ID_EXE && ~alusrc_ID_EXE)   
				alusrc2[31:0] = aluout_MEM_WB;
    	else    alusrc2[31:0] = rs2_data_ID_EXE[31:0];
	end

    always@(*)
    begin
         se_imm_itype[31:0] <= {{20{inst[31]}},inst[31:20]};
         se_imm_stype[31:0] <= {{20{inst[31]}},inst[31:25],inst[11:7]};
         auipc_lui_imm[31:0] <= {inst[31:12],12'b0};
    end


	// Data selection for writing to RF
	always@(*)
	begin
		if	     (jal_MEM_WB)			rd_data[31:0] = pc_MEM_WB + 4;
		else if (memtoreg_MEM_WB)	rd_data[31:0] = MemRdata_MEM_WB;
		else						rd_data[31:0] = aluout_MEM_WB;
	end
    
	// ###### SangJin Park: End #######
    
	
endmodule






















