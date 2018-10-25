module Controle(input wire [5:0] Opcode, 
input wire [5:0] func,
input wire [0:0] clk,
output reg [0:0] PCWrite,
output reg [0:0] PCWriteCond,
output reg [1:0] PCWriteCondMux,
output reg [2:0] MuxBranch,
output reg [2:0] MuxMemoriaEnd,
output reg [0:0] IRWrite,
output reg [0:0] RegWrite,
output reg [1:0] RegDst,
output reg [2:0] MuxULA1,
output reg [2:0] ALUControl,
output reg [0:0] ALUOutControl,
output reg [0:0] DivControl,
output reg [2:0] MuxULA2,
output reg [1:0] MuxMemoriaDado,
output reg [0:0] AControl,
output reg [0:0] BControl,
output reg [0:0] EPCCont,
output reg [0:0] MultControl,
output reg [2:0] RDControl,
output reg [0:0] MuxRD,
output reg [0:0] MuxSaidaLO,
output reg [0:0] MuxSaidaHI,
output reg [1:0] ContShifts,
output reg [3:0] MuxWriteData,
output reg [0:0] MuxHILO,
output reg [0:0] LuiControl,
output reg [0:0] MuxMDR,
output reg [2:0] ControleBits,
output reg [0:0] CHi,
output reg [0:0] CLo,
output reg [0:0] MemRead,
output reg [0:0] MDRControl);

reg [31:0] state;
///OPCODES
parameter TipoR = 6'd0;
parameter Addi = 6'd8;

//FUNC
parameter Add = 6'd32;
parameter Sub = 6'd34;
parameter Srl = 6'd0;
parameter Sra = 6'd3;
parameter Sll = 6'd2;
parameter Slt = 6'd42;
parameter And = 6'd36;
parameter Jr = 6'd8;
parameter Sllv = 6'd4;
parameter Srav = 6'd7;
parameter Break = 6'd13;
parameter Rte = 6'd19;


//ESTADOS
parameter Addi2 = 32'd09;
parameter Addi3 = 32'd010;
parameter Add1 = 32'd18;
parameter Add2 = 32'd19;
parameter Add3 = 32'd110;
parameter Add4 = 32'd111;
parameter Sub1 = 32'd28;
parameter Sub2 = 32'd29;
parameter Sub3 = 32'd210;
parameter Sub4 = 32'd211;
parameter Srl1 = 32'd38;
parameter Srl2 = 32'd39;
parameter Srl3 = 32'd310;
parameter Srl4 = 32'd311;
parameter Srl5 = 32'd312;
parameter Sra1 = 32'd48;
parameter Sra2 = 32'd49;
parameter Sra3 = 32'd410;
parameter Sra4 = 32'd411;
parameter Sra5 = 32'd412;
parameter Sll1 = 32'd58;
parameter Sll2 = 32'd59;
parameter Sll3 = 32'd510;
parameter Sll4 = 32'd511;
parameter Sll5 = 32'd512;
parameter Slt1 = 32'd68;
parameter Slt2 = 32'd69;
parameter Slt3 = 32'd610;
parameter Slt4 = 32'd611;
parameter And1 = 32'd78;
parameter And2 = 32'd79;
parameter And3 = 32'd710;
parameter And4 = 32'd711;
parameter Jr1 = 32'd88;
parameter Jr2 = 32'd89;
parameter Jr3 = 32'd810;
parameter Jr4 = 32'd811;
parameter Sllv1 = 32'd98;
parameter Sllv2 = 32'd99;
parameter Sllv3 = 32'd910;
parameter Sllv4 = 32'd911;
parameter Sllv5 = 32'd912;
parameter Srav1 = 32'd108;
parameter Srav2 = 32'd109;
parameter Srav3 = 32'd1010;
parameter Srav4 = 32'd1011;
parameter Srav5 = 32'd1012;
parameter Break1 = 32'd117;
parameter Break2 = 32'd118;
parameter Break3 = 32'd119;
parameter Break4 = 32'd1110;
parameter Break5 = 32'd1111;
parameter Rte1 = 32'd127;



//PC+4
parameter pc4 = 32'd3;

	always @(posedge clk)begin

			case(state)
				//RESET
				32'd0:
				begin
					PCWrite = 1'd0;
					PCWriteCond = 1'd0;
					PCWriteCondMux = 1'd0;
					MuxBranch = 3'd0;
					MuxMemoriaEnd = 3'd0;
					IRWrite = 1'd0;
					RegWrite = 1'd0;
					RegDst = 2'd0;
					MuxULA1 = 3'd0;
					ALUControl = 3'd0;
					ALUOutControl = 1'd0;
					DivControl = 1'd0;
					MuxULA2 = 3'd0;
					MuxMemoriaDado = 2'd0;
					AControl = 1'd0;
					BControl = 1'd0;
					EPCCont = 1'd0;
					MultControl = 1'd0;
					RDControl = 3'd0;
					MuxRD = 1'd0;
					MuxSaidaLO = 1'd0;
					MuxSaidaHI = 1'd0;
					ContShifts = 2'd0;
					MuxWriteData = 4'd0;
					MuxHILO = 1'd0;
					LuiControl = 1'd0;
					MuxMDR = 1'd0;
					ControleBits = 3'd0;
					CHi = 1'd0;
					CLo = 1'd0;
					MemRead = 1'd0;
					MDRControl = 1'd0;
					state = 32'd1;
				end
				
				32'd1:
				begin
					PCWrite = 1'd0;
					PCWriteCond = 1'd0;
					PCWriteCondMux = 1'd0;
					MuxBranch = 3'd0;
					MuxMemoriaEnd = 3'd0;
					IRWrite = 1'd0;
					RegWrite = 1'd1;
					RegDst = 2'd3;
					MuxULA1 = 3'd0;
					ALUControl = 3'd0;
					ALUOutControl = 1'd0;
					DivControl = 1'd0;
					MuxULA2 = 3'd0;
					MuxMemoriaDado = 2'd0;
					AControl = 1'd0;
					BControl = 1'd0;
					EPCCont = 1'd0;
					MultControl = 1'd0;
					RDControl = 3'd0;
					MuxRD = 1'd0;
					MuxSaidaLO = 1'd0;
					MuxSaidaHI = 1'd0;
					ContShifts = 2'd0;
					MuxWriteData = 4'b1000;
					MuxHILO = 1'd0;
					LuiControl = 1'd0;
					MuxMDR = 1'd0;
					ControleBits = 3'd0;
					CHi = 1'd0;
					CLo = 1'd0;
					MemRead = 1'd0;
					MDRControl = 1'd0;
					state = 32'd2;
				end
				
				32'd2:
				begin
					PCWrite = 1'd0;
					PCWriteCond = 1'd0;
					PCWriteCondMux = 1'd0;
					MuxBranch = 3'd0;
					MuxMemoriaEnd = 3'd0;
					IRWrite = 1'd0;
					RegWrite = 1'd0;
					RegDst = 2'd0;
					MuxULA1 = 3'd0;
					ALUControl = 3'd0;
					ALUOutControl = 1'd0;
					DivControl = 1'd0;
					MuxULA2 = 3'd0;
					MuxMemoriaDado = 2'd0;
					AControl = 1'd0;
					BControl = 1'd0;
					EPCCont = 1'd0;
					MultControl = 1'd0;
					RDControl = 3'd0;
					MuxRD = 1'd0;
					MuxSaidaLO = 1'd0;
					MuxSaidaHI = 1'd0;
					ContShifts = 2'd0;
					MuxWriteData = 4'd0;
					MuxHILO = 1'd0;
					LuiControl = 1'd0;
					MuxMDR = 1'd0;
					ControleBits = 3'd0;
					CHi = 1'd0;
					CLo = 1'd0;
					MemRead = 1'd0;
					MDRControl = 1'd0;
					state = 32'd3;
				end
				//PC+4
				32'd3:
				begin
					PCWrite = 1'd1;
					PCWriteCond = 1'd0;
					PCWriteCondMux = 1'd0;
					MuxBranch = 3'd0;
					MuxMemoriaEnd = 3'd0;
					IRWrite = 1'd0;
					RegWrite = 1'd0;
					RegDst = 2'd0;
					MuxULA1 = 3'd0;
					ALUControl = 3'd1;
					ALUOutControl = 1'd0;
					DivControl = 1'd0;
					MuxULA2 = 3'd1;
					MuxMemoriaDado = 2'd0;
					AControl = 1'd0;
					BControl = 1'd0;
					EPCCont = 1'd0;
					MultControl = 1'd0;
					RDControl = 3'd0;
					MuxRD = 1'd0;
					MuxSaidaLO = 1'd0;
					MuxSaidaHI = 1'd0;
					ContShifts = 2'd0;
					MuxWriteData = 4'd0;
					MuxHILO = 1'd0;
					LuiControl = 1'd0;
					MuxMDR = 1'd0;
					ControleBits = 3'd0;
					CHi = 1'd0;
					CLo = 1'd0;
					MemRead = 1'd0;
					MDRControl = 1'd0;
					state = 32'd4;
				end
				
				32'd4:
				begin
					PCWrite = 1'd0;
					PCWriteCond = 1'd0;
					PCWriteCondMux = 1'd0;
					MuxBranch = 3'd0;
					MuxMemoriaEnd = 3'd0;
					IRWrite = 1'd0;
					RegWrite = 1'd0;
					RegDst = 2'd0;
					MuxULA1 = 3'd0;
					ALUControl = 3'd0;
					ALUOutControl = 1'd0;
					DivControl = 1'd0;
					MuxULA2 = 3'd0;
					MuxMemoriaDado = 2'd0;
					AControl = 1'd0;
					BControl = 1'd0;
					EPCCont = 1'd0;
					MultControl = 1'd0;
					RDControl = 3'd0;
					MuxRD = 1'd0;
					MuxSaidaLO = 1'd0;
					MuxSaidaHI = 1'd0;
					ContShifts = 2'd0;
					MuxWriteData = 4'd0;
					MuxHILO = 1'd0;
					LuiControl = 1'd0;
					MuxMDR = 1'd0;
					ControleBits = 3'd0;
					CHi = 1'd0;
					CLo = 1'd0;
					MemRead = 1'd0;
					MDRControl = 1'd0;
					state = 32'd5;
				end
				
				32'd5:
				begin
					PCWrite = 1'd0;
					PCWriteCond = 1'd0;
					PCWriteCondMux = 1'd0;
					MuxBranch = 3'd0;
					MuxMemoriaEnd = 3'd0;
					IRWrite = 1'd1;
					RegWrite = 1'd0;
					RegDst = 2'd0;
					MuxULA1 = 3'd0;
					ALUControl = 3'd0;
					ALUOutControl = 1'd0;
					DivControl = 1'd0;
					MuxULA2 = 3'd0;
					MuxMemoriaDado = 2'd0;
					AControl = 1'd0;
					BControl = 1'd0;
					EPCCont = 1'd0;
					MultControl = 1'd0;
					RDControl = 3'd0;
					MuxRD = 1'd0;
					MuxSaidaLO = 1'd0;
					MuxSaidaHI = 1'd0;
					ContShifts = 2'd0;
					MuxWriteData = 4'd0;
					MuxHILO = 1'd0;
					LuiControl = 1'd0;
					MuxMDR = 1'd0;
					ControleBits = 3'd0;
					CHi = 1'd0;
					CLo = 1'd0;
					MemRead = 1'd0;
					MDRControl = 1'd0;
					state = 32'd6;
				end
				
				32'd6:
				begin
					PCWrite = 1'd0;
					PCWriteCond = 1'd0;
					PCWriteCondMux = 1'd0;
					MuxBranch = 3'd0;
					MuxMemoriaEnd = 3'd0;
					IRWrite = 1'd0;
					RegWrite = 1'd0;
					RegDst = 2'd0;
					MuxULA1 = 3'd0;
					ALUControl = 3'd0;
					ALUOutControl = 1'd0;
					DivControl = 1'd0;
					MuxULA2 = 3'd0;
					MuxMemoriaDado = 2'd0;
					AControl = 1'd0;
					BControl = 1'd0;
					EPCCont = 1'd0;
					MultControl = 1'd0;
					RDControl = 3'd0;
					MuxRD = 1'd0;
					MuxSaidaLO = 1'd0;
					MuxSaidaHI = 1'd0;
					ContShifts = 2'd0;
					MuxWriteData = 4'd0;
					MuxHILO = 1'd0;
					LuiControl = 1'd0;
					MuxMDR = 1'd0;
					ControleBits = 3'd0;
					CHi = 1'd0;
					CLo = 1'd0;
					MemRead = 1'd0;
					MDRControl = 1'd0;
					state = 32'd7;
				end
				32'd7:
				begin
					case(Opcode)
						TipoR:	
						begin
							case(func)
							//ADD
								Add:
								begin
									state = Add1;
								end
							//SUB
								Sub:
								begin
									state = Sub1;
								end
							//SRL
								Srl:
								begin
									state = Srl1;
								end
							//SRA
								Sra:
								begin
									state = Sra1;
								end
							//SLL
								Sll:
								begin
									state = Sll1;
								end
							//SLT
								Slt:
								begin
									state = Slt1;
								end
							//AND
								And:
								begin
									state = And1;
								end
							//JR
								Jr:
								begin
									state = Jr1;
								end
							//SLLV
								Sllv:
								begin
								state = Sllv1;
								end
							//SRAV
								Srav:
								begin
								state = Srav1;
								end
							//BREAK
								Break:
								begin
								state = Break1;
								end
							//RTE
								Rte:
								begin
								state = Rte1;
								end
								default:
								begin
								state = pc4;
								end
							endcase
						end
						//ADDI
						Addi:
						begin
							state = Addi;
						end
						default:
							begin
							state = pc4;
							end
					endcase
				end
				//ADDI
				Addi:
				begin
					PCWrite = 1'd0;
					PCWriteCond = 1'd0;
					PCWriteCondMux = 1'd0;
					MuxBranch = 3'd0;
					MuxMemoriaEnd = 3'd0;
					IRWrite = 1'd0;
					RegWrite = 1'd0;
					RegDst = 2'd0;
					MuxULA1 = 3'b100;
					ALUControl = 3'd1;
					ALUOutControl = 1'd1;
					DivControl = 1'd0;
					MuxULA2 = 3'b010;
					MuxMemoriaDado = 2'd0;
					AControl = 1'd1;
					BControl = 1'd0;
					EPCCont = 1'd0;
					MultControl = 1'd0;
					RDControl = 3'd0;
					MuxRD = 1'd0;
					MuxSaidaLO = 1'd0;
					MuxSaidaHI = 1'd0;
					ContShifts = 2'd0;
					MuxWriteData = 4'd0;
					MuxHILO = 1'd0;
					LuiControl = 1'd0;
					MuxMDR = 1'd0;
					ControleBits = 3'd0;
					CHi = 1'd0;
					CLo = 1'd0;
					MemRead = 1'd0;
					MDRControl = 1'd0;
					state = Addi2;
				end
				Addi2:
				begin
					state = Addi3;
				end
				Addi3:
				begin
					PCWrite = 1'd0;
					PCWriteCond = 1'd0;
					PCWriteCondMux = 1'd0;
					MuxBranch = 3'd0;
					MuxMemoriaEnd = 3'd0;
					IRWrite = 1'd0;
					RegWrite = 1'd1;
					RegDst = 2'd0;
					MuxULA1 = 3'd0;
					ALUControl = 3'd0;
					ALUOutControl = 1'd0;
					DivControl = 1'd0;
					MuxULA2 = 3'd0;
					MuxMemoriaDado = 2'd0;
					AControl = 1'd0;
					BControl = 1'd0;
					EPCCont = 1'd0;
					MultControl = 1'd0;
					RDControl = 3'd0;
					MuxRD = 1'd0;
					MuxSaidaLO = 1'd0;
					MuxSaidaHI = 1'd0;
					ContShifts = 2'd0;
					MuxWriteData = 4'd0;
					MuxHILO = 1'd0;
					LuiControl = 1'd0;
					MuxMDR = 1'd0;
					ControleBits = 3'd0;
					CHi = 1'd0;
					CLo = 1'd0;
					MemRead = 1'd0;
					MDRControl = 1'd0;
					state = pc4;
				end
				
				//SUB
				Sub1:
				begin
					PCWrite = 1'd0;
					PCWriteCond = 1'd0;
					PCWriteCondMux = 1'd0;
					MuxBranch = 3'd0;
					MuxMemoriaEnd = 3'd0;
					IRWrite = 1'd0;
					RegWrite = 1'd0;
					RegDst = 2'd0;
					MuxULA1 = 3'b100;
					ALUControl = 3'b010;
					ALUOutControl = 1'd1;
					DivControl = 1'd0;
					MuxULA2 = 3'd0;
					MuxMemoriaDado = 2'd0;
					AControl = 1'd1;
					BControl = 1'd1;
					EPCCont = 1'd0;
					MultControl = 1'd0;
					RDControl = 3'd0;
					MuxRD = 1'd0;
					MuxSaidaLO = 1'd0;
					MuxSaidaHI = 1'd0;
					ContShifts = 2'd0;
					MuxWriteData = 4'd0;
					MuxHILO = 1'd0;
					LuiControl = 1'd0;
					MuxMDR = 1'd0;
					ControleBits = 3'd0;
					CHi = 1'd0;
					CLo = 1'd0;
					MemRead = 1'd0;
					MDRControl = 1'd0;
					state = Sub2;
				end
				Sub2:
				begin
					state = Sub3;
				end
				Sub3:
				begin
					PCWrite = 1'd0;
					PCWriteCond = 1'd0;
					PCWriteCondMux = 1'd0;
					MuxBranch = 3'd0;
					MuxMemoriaEnd = 3'd0;
					IRWrite = 1'd0;
					RegWrite = 1'd1;
					RegDst = 2'd1;
					MuxULA1 = 3'd0;
					ALUControl = 3'b010;
					ALUOutControl = 1'd0;
					DivControl = 1'd0;
					MuxULA2 = 3'd0;
					MuxMemoriaDado = 2'd0;
					AControl = 1'd0;
					BControl = 1'd0;
					EPCCont = 1'd0;
					MultControl = 1'd0;
					RDControl = 3'd0;
					MuxRD = 1'd0;
					MuxSaidaLO = 1'd0;
					MuxSaidaHI = 1'd0;
					ContShifts = 2'd0;
					MuxWriteData = 4'd0;
					MuxHILO = 1'd0;
					LuiControl = 1'd0;
					MuxMDR = 1'd0;
					ControleBits = 3'd0;
					CHi = 1'd0;
					CLo = 1'd0;
					MemRead = 1'd0;
					MDRControl = 1'd0;
					state = Sub4;
				end
				Sub4:
				begin
					PCWrite = 1'd0;
					PCWriteCond = 1'd0;
					PCWriteCondMux = 1'd0;
					MuxBranch = 3'd0;
					MuxMemoriaEnd = 3'd0;
					IRWrite = 1'd0;
					RegWrite = 1'd0;
					RegDst = 2'd0;
					MuxULA1 = 3'd0;
					ALUControl = 3'd0;
					ALUOutControl = 1'd0;
					DivControl = 1'd0;
					MuxULA2 = 3'd0;
					MuxMemoriaDado = 2'd0;
					AControl = 1'd0;
					BControl = 1'd0;
					EPCCont = 1'd0;
					MultControl = 1'd0;
					RDControl = 3'd0;
					MuxRD = 1'd0;
					MuxSaidaLO = 1'd0;
					MuxSaidaHI = 1'd0;
					ContShifts = 2'd0;
					MuxWriteData = 4'd0;
					MuxHILO = 1'd0;
					LuiControl = 1'd0;
					MuxMDR = 1'd0;
					ControleBits = 3'd0;
					CHi = 1'd0;
					CLo = 1'd0;
					MemRead = 1'd0;
					MDRControl = 1'd0;
					state = pc4;
				end		
			
				//SRL
				Srl1:
				begin
				AControl =1'b1;
				BControl =1'b1;
				ContShifts =2'b10;
				MuxULA1 = 3'b100;
				MuxULA2 = 3'b000;
				MuxRD = 1'b1;
				state = Srl2;
				end
				Srl2:
				begin
					AControl = 1'b0;
					BControl = 1'b0;
					RDControl = 3'b011;
					state = Srl3;
				end
				Srl3:
				begin
					RegDst = 1'b1;
					MuxWriteData = 3'b100;
					RegWrite= 1'b1;
					state = Srl4;
				end
				Srl4:
				begin
					state = Srl5;
				end
				Srl5:
				begin
					RegWrite = 1'b0;
					state = pc4;
				end
				
				//SRA
				Sra1:
				begin
				AControl =1'b1;
				BControl =1'b1;
				ContShifts =2'b10;
				MuxULA1 = 3'b100;
				MuxULA2 = 3'b000;
				MuxRD = 1'b1;
				state = Sra2;
				end
				Sra2:
				begin
					AControl = 1'b0;
					BControl = 1'b0;
					RDControl = 3'b100;
					state = Sra3;
				end	
				Sra3:
				begin
					RegDst = 1'b1;
					MuxWriteData = 3'b100;
					RegWrite= 1'b1;
					state = Sra4;
				end
				Sra4:
				begin
					state = Sra5;
				end
				Sra5:
				begin
					RegWrite = 1'b0;
					state = pc4;
				end
				
				//SLL 
				Sll1:
				begin
				AControl =1'b1;
				BControl =1'b1;
				ContShifts =2'b10;
				MuxULA1 = 3'b100;
				MuxULA2 = 3'b000;
				MuxRD = 1'b1;
				state = Sll2;
				end
				Sll2:
				begin
					AControl = 1'b0;
					BControl = 1'b0;
					RDControl = 3'b010;
					state = Sll3;
				end	
				Sll3:
				begin
					RegDst = 1'b1;
					MuxWriteData = 3'b100;
					RegWrite= 1'b1;
					state = Sll4;
				end	
				Sll4:
				begin
					state = Sll5;
				end
				Sll5:
				begin
					RegWrite = 1'b0;
					state = pc4;
				end
				
				//SLT
				Slt1:
				begin
					AControl = 1'b1;
					BControl = 1'b1;
					MuxULA1 = 3'b100;
					MuxULA2 = 3'b000;
					ALUControl = 3'b111;
					state = Slt2;
				end	
				Slt2:
				begin
					AControl = 1'b0;
					BControl = 1'b0;
					MuxWriteData = 3'b011;
					RegDst = 2'b01;
					RegWrite = 1'b1;
					state = Slt3;
				end
				Slt3:
				begin
					state = Slt4;
				end		
				Slt4:
				begin
					RegWrite = 1'b0;
					state = pc4;
				end
				//JR
				Jr1:
				begin
					MuxULA1 = 3'b011;
					MuxULA2 = 3'b101;
					ALUControl = 3'b001;
					ALUOutControl = 1'b1;
					state = Jr2;
				end		
				Jr2:
				begin
					MuxBranch = 2'b10;
					ALUOutControl = 1'b0;
					PCWrite = 1'b1;
					state = Jr3;
				end		
				Jr3:
				begin
					state = Jr4;
				end		
				Jr4:
				begin
					PCWrite = 1'b0;
					state = pc4;
				end
			
				//SLLV
				Sllv1:
				begin
					ContShifts = 2'b01;
					MuxULA1 = 3'b100;
					MuxRD = 1'b0;
					state = Sllv2;
				end
				Sllv2:
				begin
					RDControl = 3'b010;
					state = Sllv3;
				end				
				Sllv3:
				begin
					RegDst = 1'b1;
					MuxWriteData = 3'b100;
					RegWrite = 1'b1;
					state = Sllv4;
				end				
				Sllv4:
				begin
					state = Sllv5;
				end			
				Sllv5:
				begin
					RegWrite = 1'b0;
					state = pc4;
				end
				
				//SRAV
				Srav1:
				begin
					ContShifts = 2'b01;
					MuxULA1 = 3'b100;
					MuxRD = 1'b0;
					state = Srav2;
				end	
				Srav2:
				begin
					RDControl = 3'b100;
					state = Srav3;
				end
				Srav3:
				begin
					RegDst = 1'b1;
					MuxWriteData = 3'b100;
					RegWrite = 1'b1;
					state = Srav4;
				end
				Srav4:
				begin
					state = Srav5;
				end
				Srav5:
				begin
					RegWrite = 1'b0;
					state = pc4;
				end
				
				//Break
				Break1:
				begin
					AControl = 1'b1;
					BControl = 1'b1;
					MuxULA1 = 3'b000;
					MuxULA2 = 3'b001;
					ALUControl = 3'b010;
					state = Break2;
				end
				Break2:
				begin
					AControl = 1'b0;
					BControl = 1'b0;
					MuxBranch = 3'b000;
					PCWrite = 1'b1;
					state = Break3;
				end
				Break3:
				begin
					state =Break4;
				end
				Break4:
				begin
					state =Break5;
				end
				Break5:
				begin
					PCWrite = 1'b0;
					state =pc4;
				end
				
				//RTE
				Rte1:
				begin
					MuxBranch = 1'b1;
					PCWrite = 1'b1;
					state = pc4;
				end
				
				And1:
				begin 
					PCWrite = 1'd0;
					PCWriteCond = 1'd0;
					PCWriteCondMux = 1'd0;
					MuxBranch = 3'd0;
					MuxMemoriaEnd = 3'd0;
					IRWrite = 1'd0;
					RegWrite = 1'd0;
					RegDst = 2'd0;
					MuxULA1 = 3'b100;
					ALUControl = 3'b011;
					ALUOutControl = 1'd1;
					DivControl = 1'd0;
					MuxULA2 = 3'd0;
					MuxMemoriaDado = 2'd0;
					AControl = 1'd1;
					BControl = 1'd1;
					EPCCont = 1'd0;
					MultControl = 1'd0;
					RDControl = 3'd0;
					MuxRD = 1'd0;
					MuxSaidaLO = 1'd0;
					MuxSaidaHI = 1'd0;
					ContShifts = 2'd0;
					MuxWriteData = 4'd0;
					MuxHILO = 1'd0;
					LuiControl = 1'd0;
					MuxMDR = 1'd0;
					ControleBits = 3'd0;
					CHi = 1'd0;
					CLo = 1'd0;
					MemRead = 1'd0;
					MDRControl = 1'd0;
					state = Add2;
				end
				And2:
				begin
					state = Add3;
				end
				And3:
				begin
					PCWrite = 1'd0;
					PCWriteCond = 1'd0;
					PCWriteCondMux = 1'd0;
					MuxBranch = 3'd0;
					MuxMemoriaEnd = 3'd0;
					IRWrite = 1'd0;
					RegWrite = 1'd1;
					RegDst = 2'b01;
					MuxULA1 = 3'd0;
					ALUControl = 3'd0;
					ALUOutControl = 1'd0;
					DivControl = 1'd0;
					MuxULA2 = 3'd0;
					MuxMemoriaDado = 2'd0;
					AControl = 1'd0;
					BControl = 1'd0;
					EPCCont = 1'd0;
					MultControl = 1'd0;
					RDControl = 3'd0;
					MuxRD = 1'd0;
					MuxSaidaLO = 1'd0;
					MuxSaidaHI = 1'd0;
					ContShifts = 2'd0;
					MuxWriteData = 4'd0;
					MuxHILO = 1'd0;
					LuiControl = 1'd0;
					MuxMDR = 1'd0;
					ControleBits = 3'd0;
					CHi = 1'd0;
					CLo = 1'd0;
					MemRead = 1'd0;
					MDRControl = 1'd0;
					state = Add4;
				end
				And4:
				begin
					PCWrite = 1'd0;
					PCWriteCond = 1'd0;
					PCWriteCondMux = 1'd0;
					MuxBranch = 3'd0;
					MuxMemoriaEnd = 3'd0;
					IRWrite = 1'd0;
					RegWrite = 1'd0;
					RegDst = 2'd0;
					MuxULA1 = 3'd0;
					ALUControl = 3'd0;
					ALUOutControl = 1'd0;
					DivControl = 1'd0;
					MuxULA2 = 3'd0;
					MuxMemoriaDado = 2'd0;
					AControl = 1'd0;
					BControl = 1'd0;
					EPCCont = 1'd0;
					MultControl = 1'd0;
					RDControl = 3'd0;
					MuxRD = 1'd0;
					MuxSaidaLO = 1'd0;
					MuxSaidaHI = 1'd0;
					ContShifts = 2'd0;
					MuxWriteData = 4'd0;
					MuxHILO = 1'd0;
					LuiControl = 1'd0;
					MuxMDR = 1'd0;
					ControleBits = 3'd0;
					CHi = 1'd0;
					CLo = 1'd0;
					MemRead = 1'd0;
					MDRControl = 1'd0;
					state = pc4;
				end
				Add1:
				begin
					PCWrite = 1'd0;
					PCWriteCond = 1'd0;
					PCWriteCondMux = 1'd0;
					MuxBranch = 3'd0;
					MuxMemoriaEnd = 3'd0;
					IRWrite = 1'd0;
					RegWrite = 1'd0;
					RegDst = 2'd0;
					MuxULA1 = 3'b100;
					ALUControl = 3'b001;
					ALUOutControl = 1'd1;
					DivControl = 1'd0;
					MuxULA2 = 3'b000;
					MuxMemoriaDado = 2'd0;
					AControl = 1'd1;
					BControl = 1'd1;
					EPCCont = 1'd0;
					MultControl = 1'd0;
					RDControl = 3'd0;
					MuxRD = 1'd0;
					MuxSaidaLO = 1'd0;
					MuxSaidaHI = 1'd0;
					ContShifts = 2'd0;
					MuxWriteData = 4'd0;
					MuxHILO = 1'd0;
					LuiControl = 1'd0;
					MuxMDR = 1'd0;
					ControleBits = 3'd0;
					CHi = 1'd0;
					CLo = 1'd0;
					MemRead = 1'd0;
					MDRControl = 1'd0;
					state= Add2;
				end
				
				Add2:
				begin
					state = Add3;
				end
				
				Add3:
				begin
					PCWrite = 1'd0;
					PCWriteCond = 1'd0;
					PCWriteCondMux = 1'd0;
					MuxBranch = 3'd0;
					MuxMemoriaEnd = 3'd0;
					IRWrite = 1'd0;
					RegWrite = 1'd1;
					RegDst = 2'd1;
					MuxULA1 = 3'd0;
					ALUControl = 3'd0;
					ALUOutControl = 1'd0;
					DivControl = 1'd0;
					MuxULA2 = 3'd0;
					MuxMemoriaDado = 2'd0;
					AControl = 1'd0;
					BControl = 1'd0;
					EPCCont = 1'd0;
					MultControl = 1'd0;
					RDControl = 3'd0;
					MuxRD = 1'd0;
					MuxSaidaLO = 1'd0;
					MuxSaidaHI = 1'd0;
					ContShifts = 2'd0;
					MuxWriteData = 4'd0;
					MuxHILO = 1'd0;
					LuiControl = 1'd0;
					MuxMDR = 1'd0;
					ControleBits = 3'd0;
					CHi = 1'd0;
					CLo = 1'd0;
					MemRead = 1'd0;
					MDRControl = 1'd0;
					state = Add4;
				end
				
				Add4:
				begin
					PCWrite = 1'd0;
					PCWriteCond = 1'd0;
					PCWriteCondMux = 1'd0;
					MuxBranch = 3'd0;
					MuxMemoriaEnd = 3'd0;
					IRWrite = 1'd0;
					RegWrite = 1'd0;
					RegDst = 2'd0;
					MuxULA1 = 3'd0;
					ALUControl = 3'd0;
					ALUOutControl = 1'd0;
					DivControl = 1'd0;
					MuxULA2 = 3'd0;
					MuxMemoriaDado = 2'd0;
					AControl = 1'd0;
					BControl = 1'd0;
					EPCCont = 1'd0;
					MultControl = 1'd0;
					RDControl = 3'd0;
					MuxRD = 1'd0;
					MuxSaidaLO = 1'd0;
					MuxSaidaHI = 1'd0;
					ContShifts = 2'd0;
					MuxWriteData = 4'd0;
					MuxHILO = 1'd0;
					LuiControl = 1'd0;
					MuxMDR = 1'd0;
					ControleBits = 3'd0;
					CHi = 1'd0;
					CLo = 1'd0;
					MemRead = 1'd0;
					MDRControl = 1'd0;
					state = pc4;
				end
				
				default:
					begin
					state = pc4;
					end
			endcase	
				
		end
endmodule