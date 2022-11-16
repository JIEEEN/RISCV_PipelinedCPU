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

  wire        auipc, lui;
  wire        alusrc, regwrite;
  wire [4:0]  alucontrol;
  wire        memtoreg, memwrite;
  wire        branch, jal, jalr;

  assign Memwrite = memwrite ;

  // Instantiate Controller
  controller i_controller(
      .opcode		(inst[6:0]), 
		.funct7		(inst[31:25]), 
		.funct3		(inst[14:12]), 
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
		.inst				(inst),
		.aluout			(Memaddr), 
		.MemWdata		(MemWdata),
		.MemRdata		(MemRdata));

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
`define OP_I_JALR  	7'b1100111		////////////////////////////////
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
      `OP_I_JALR: 	controls <= #`simdelay 9'b0011_0000_1; // jalr
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
          default:         alucontrol <= #`simdelay 5'bxxxxx; // ???
        endcase
		end

      `OP_I_ARITH:   // I-type Arithmetic
		begin
			case(funct3)
			 3'b000:  alucontrol <= #`simdelay 5'b00000; // addition (addi)
			 3'b110:  alucontrol <= #`simdelay 5'b00010; // or (ori)
			 3'b100:  alucontrol <= #`simdelay 5'b00011; // xori 
			 3'b111:  alucontrol <= #`simdelay 5'b00001; // and (andi)
			 3'b001:  alucontrol <= #`simdelay 5'b00100; // slli (=sll) Jin
          default: alucontrol <= #`simdelay 5'bxxxxx; // ???
        endcase
		end

      `OP_I_LOAD:												// I-type Load (LW, LH, LB...)
			alucontrol <= #`simdelay 5'b00000;
      `OP_I_JALR: 											// I-type (JALR)
			alucontrol <= #`simdelay 5'b00000;
      `OP_S:  													// S-type Store (SW, SH, SB)
			alucontrol <= #`simdelay 5'b00000;
      `OP_U_LUI: 												// U-type (LUI)
			alucontrol <= #`simdelay 5'b00000;
      `OP_U_AUIPC: 											// U-type (AUIPC)
      		alucontrol <= #`simdelay 5'b00000;  		// addition 

      `OP_B:   												// B-type Branch (BEQ, BNE, ...)
      	alucontrol <= #`simdelay 5'b10000;  // subtraction 

      default: 
      	alucontrol <= #`simdelay 5'b00000;  //

    endcase
    
endmodule


//
// DATA_FORWARDING
//
module Forward_Unit(input  [4:0] rs1_EXE,
						  input  [4:0] rs2_EXE,
						  input  [4:0] rd_MEM,
						  input  [4:0] rd_WB,
						  output reg [1:0] forward_1,
						  output reg [1:0] forward_2);

	always @(*)
		begin
			if (rd_WB[4:0] == rs1_EXE[4:0])
				forward_1 = 2'b10;
			else if (rd_MEM[4:0] == rs1_EXE[4:0])
				forward_1 = 2'b01;
			else forward_1 = 2'b00;
		end
	
	always @(*)
		begin
			if (rd_WB[4:0] == rs2_EXE[4:0])
				forward_2 = 2'b10;
			else if (rd_MEM[4:0] == rs2_EXE[4:0])
				forward_2 = 2'b01;
			else forward_2 = 2'b00;
		end
		
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
                output [31:0] aluout,
                output [31:0] MemWdata,
                input  [31:0] MemRdata);

  wire [4:0]  rs1, rs2, rd;
  reg [4:0]  rd_ID_EXE, rd_EXE_MEM, rd_MEM_WB; // rd extended with FF
  wire [2:0]  funct3;
  wire [31:0] rs1_data, rs2_data; //del?
  reg  [31:0] rd_data;
  wire [20:1] jal_imm;
  wire [31:0] se_jal_imm;
  reg  [31:0] se_jal_imm_ff; //ff
  wire [12:1] br_imm;
  wire [31:0] se_br_imm;
  reg  [31:0] se_br_imm_ff; //ff
  wire [31:0] se_imm_itype;
  wire [31:0] se_imm_stype; 
  wire [31:0] auipc_lui_imm;
  reg  [31:0] alusrc1;
  reg  [31:0] alusrc2;
  reg  [31:0] rs1_data_ID_EXE; //ff
  reg	 [31:0] rs2_data_ID_EXE; //ff
  reg  [31:0] rs2_data_EXE_MEM; //ff
  reg  [31:0] MemRdata_ff; //ff
  reg  [31:0] aluout_EXE_MEM; //ff
  reg  [31:0] aluout_MEM_WB; //ff
  
  reg 		auipc_ff; //ff
  reg			lui_ff; //ff
  reg 		alusrc_ff; //ff 
  reg [4:0] alucontrol_ff; //ff
  reg 		jal_ff, jalr_ff; //ff
  
  reg			regwrite_ff; //ff
  reg			memtoreg_ff; //ff
  reg			memwrite_ff; //ff
  
  wire [31:0] branch_dest, jal_dest, jalr_dest;		
  wire		  Nflag, Zflag, Cflag, Vflag;
  wire		  f3beq, f3blt, f3bgeu;
  wire		  beq_taken;
  wire		  blt_taken;
  wire		  bgeu_taken;	
  wire		  btaken;
  
  reg  [31:0] pc_IF_ID, pc_ID_EXE; //ff
  reg  [31:0] inst_ff; //ff

  assign rs1 = inst_ff[19:15];
  assign rs2 = inst_ff[24:20];
  assign rd  = inst_ff[11:7];
  assign funct3  = inst_ff[14:12];

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

  assign branch_dest = (pc_ID_EXE + se_br_imm_ff); //chg : (pc + se_br_imm) -> (pc_ID_EXE + se_br_imm_ff)
  assign jal_dest 	= (pc_ID_EXE + se_jal_imm_ff); //chg : (pc + se_jal_imm) -> (pc_ID_EXE + se_jal_imm_ff)
  assign jalr_dest   = {aluout_EXE_MEM[31:1],1'b0};	///////////***********************?////////////////

  always @(posedge clk, posedge reset) //1
  begin
     if (reset)  pc <= 32'b0;
	  else 
	  begin
	      if (btaken) // branch_taken
				pc <= #`simdelay branch_dest;
		   else if (jal_ff) // jal
				pc <= #`simdelay jal_dest;
			else if (jalr_ff)
				pc <= #`simdelay jalr_dest;	
		   else 
				pc <= #`simdelay (pc + 4);
	  end
  end


  // JAL immediate
  assign jal_imm[20:1] = {inst_ff[31],inst_ff[19:12],inst_ff[20],inst_ff[30:21]};
  assign se_jal_imm[31:0] = {{11{jal_imm[20]}},jal_imm[20:1],1'b0};

  // Branch immediate
  assign br_imm[12:1] = {inst_ff[31],inst_ff[7],inst_ff[30:25],inst_ff[11:8]};
  assign se_br_imm[31:0] = {{19{br_imm[12]}},br_imm[12:1],1'b0};



  // 
  // Register File 
  //
  regfile i_regfile(
    .clk			(clk),
    .we			(regwrite_ff),
    .rs1			(rs1),
    .rs2			(rs2),
    .rd			(rd_MEM_WB),
    .rd_data	(rd_data),
    .rs1_data	(rs1_data),
    .rs2_data	(rs2_data));


	assign MemWdata = rs2_data_EXE_MEM;
	
	always @(posedge clk) //2
		begin
			pc_IF_ID <= pc;
		end
		
	always @(posedge clk) //3
		begin
			inst_ff <= inst;
		end
		
	always @(posedge clk) //4
		begin	
			auipc_ff <= auipc;
			lui_ff <= lui;
			alusrc_ff <= alusrc;
			alucontrol_ff <= alucontrol;
			jal_ff <= jal;
			jalr_ff <= jalr;
		end
		
	always @(posedge clk) //5
		begin
			pc_ID_EXE <= pc_IF_ID;
		end

	
	always @(posedge clk) //6
		begin
			rs1_data_ID_EXE <= rs1_data;
		end
	
	always @(posedge clk) //7
		begin
			rs2_data_ID_EXE <= rs2_data;
		end

		
	always @(posedge clk) //8
		begin
			rd_ID_EXE <= rd;
		end
		
	always @(posedge clk) //9
		begin
			se_br_imm_ff <= se_br_imm;
			se_jal_imm_ff <= se_jal_imm;
		end
		
	always @(posedge clk) //10
		begin
			memwrite_ff <= memwrite;
		end
		
	always @(posedge clk) //11
		begin
			rs2_data_EXE_MEM <= rs2_data_ID_EXE;
		end
		
	always @(posedge clk) //12
		begin
			aluout_EXE_MEM <= aluout;
		end

	always @(posedge clk) //13
		begin
			rd_EXE_MEM <= rd_ID_EXE;
		end
	
	always @(posedge clk) //14
		begin
			regwrite_ff <= regwrite;
			memtoreg_ff <= memtoreg;
		end
		
	always @(posedge clk) //15
		begin
			MemRdata_ff <= MemRdata;
		end
		
	always @(posedge clk) //16
		begin
			aluout_MEM_WB <=  aluout_EXE_MEM;
		end	
		
	always @(posedge clk) //17
		begin
			rd_MEM_WB <= rd_EXE_MEM;
		end
		
		
	

	//
	// ALU 
	//
	alu i_alu(
		.a			(alusrc1), //chg : alusrc1 -> alusrc1_ff
		.b			(alusrc2), //chg : alusrc2 -> alusrc2_ff
		.alucont	(alucontrol_ff),
		.result	(aluout),
		.N			(Nflag),
		.Z			(Zflag),
		.C			(Cflag),
		.V			(Vflag));

	// 1st source to ALU (alusrc1)
	always@(*)
	begin
		if      (auipc_ff)	alusrc1[31:0]  =  pc; //chg : auipc -> auipc_ff
		else if (lui_ff) 		alusrc1[31:0]  =  32'b0;
		else          		alusrc1[31:0]  =  rs1_data_ID_EXE; //chg : rs1_data[31:0] -> rs1_data_ID_EXE
	end
	
	// 2nd source to ALU (alusrc2)
	always@(*)
	begin
		if	     (auipc_ff | lui_ff)			alusrc2[31:0] = auipc_lui_imm[31:0]; //chg : auipc -> auipc_ff
		else if (alusrc_ff & memwrite_ff)	alusrc2[31:0] = se_imm_stype[31:0]; //chg : alusrc -> alusrc_ff
		else if (alusrc_ff)					alusrc2[31:0] = se_imm_itype[31:0]; //chg : alusrc -> alusrc_ff
		else									alusrc2[31:0] = rs2_data_ID_EXE; //chg : rs2_data[31:0] -> rs2_data_ID_EXE
	end
	
	assign se_imm_itype[31:0] = {{20{inst_ff[31]}},inst_ff[31:20]}; //inst -> inst_ff
	assign se_imm_stype[31:0] = {{20{inst_ff[31]}},inst_ff[31:25],inst_ff[11:7]}; //inst -> inst_ff
	assign auipc_lui_imm[31:0] = {inst_ff[31:12],12'b0}; //inst -> inst_ff


	// Data selection for writing to RF
	always@(*)
	begin
		if	     (jal_ff | jalr_ff)			rd_data[31:0] = pc + 4;
		else if (memtoreg_ff)	rd_data[31:0] = MemRdata_ff;
		else						rd_data[31:0] = aluout_MEM_WB; //chg : aluout -> aluout_MEM_WB;
	end
	
endmodule
