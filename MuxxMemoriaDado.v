module MuxxMemoriaDado (input wire[1:0] MuxMemoriaDado, input wire [31:0] BFio, input wire [31:0] SaidaAritDadoFio,
						 input wire [31:0] QtdBitsDadoFio , output reg [31:0] MuxDadoFio); 	
	
	always begin
		case(MuxMemoriaDado)
			2'b00: 
			begin
			MuxDadoFio <= BFio;
			end
			
			2'b01:
			begin
			MuxDadoFio <= SaidaAritDadoFio;
			end
			
			2'b10:
			begin
			MuxDadoFio <= QtdBitsDadoFio;
			end
		
		endcase
	end
 
	

endmodule