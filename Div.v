module Div(input wire DivControl, input wire Reset, input wire [31:0] AFio, input wire clk,
	input wire [31:0] BFio, output reg [31:0] DivLoFio, output reg [31:0] DivHiFio, output reg DivZero);
 
reg [64:0] P;
reg [64:0] A;
reg [1:0] estado;
reg [4:0] contador;

parameter WHILE = 2'b00;
parameter INITIAL = 2'b01;
parameter REPEAT = 2'b10;
parameter END = 2'b11;

initial begin 
	estado = WHILE;
	DivZero = 1'b0;
end
 
always @(posedge clk) begin
	if (DivControl == 1'b1 && estado == WHILE) begin
		if (BFio == 32'd0) 
			begin
				DivZero = 1'b1;
				estado = WHILE;
			end 
		else
			begin
			DivZero = 1'b0;
			estado = INITIAL;
			DivLoFio = {32{1'b0}};
			DivHiFio = {32{1'b0}};
			end
	end else if (Reset == 1'b1 && estado == WHILE) begin
		P = 65'd0;
		A = 65'd0;
		estado = 2'd0;
		contador = 5'd0;
		DivHiFio = 32'd0;
		DivLoFio = 32'd0;
		DivZero = 1'd0;
	end
	
	case(estado)
				
		INITIAL:
		begin
			DivZero = 1'b0;
			contador = {5{1'b1}};
			if (BFio[31] == 1)
				A = {1'b1, BFio, {32{1'b0}}};
			else
				A = {1'b0, BFio, {32{1'b0}}};
			if (AFio[31] == 1)
				P = {{33{1'b1}}, AFio};
			else
				P = {{33{1'b0}}, AFio};
			if (BFio[31] == 1) begin
				P = -P;
				A = -A;
			end
			P = P << 1;
			if (P[64] == 1'b1)
				P = P + A;
			else
				P = P - A;
			if (P[64] == 1'b0)
				P[0] = 1'b1;
			contador = contador - 1;
			estado = REPEAT;
		end
		
		REPEAT:
		begin
			P = P << 1;
			if (P[64] == 1'b1)
				P = P + A;
			else
				P = P - A;
			if (P[64] == 1'b0)
				P[0] = 1'b1;
				
			contador = contador - 1;
			if (contador == 5'd0)
				estado = END;	
		end
		
		END:
		begin
			P = P << 1;
			if (P[64] == 1'b1)
				P = P + A;
			else
				P = P - A;
			if (P[64] == 1'b0)
				P[0] = 1'b1;
			if (P[64] == 1'b1)
			begin
				if (P[64] == 1'b1)
					P = P + A;
				else
					P = P - A;
			end
			DivHiFio = P[63:32];
			DivLoFio = P[31:0];
			estado = WHILE;
		end
	endcase
end

endmodule

/*
65 BITS - 4 REGISTRADORES - P - A
CONTADOR 5 BITS
ESTADOS 2 BITS

-----INITIAL
ZERA TUDO
COLOCA 32 BITS 0 A DIREITA DO DIVISOR (A)
EXTENDER O BIT DO SINAL EM 1 (ESQUERDA) - se a for negativo

JOGA 33 ZEROS NA ESQUERDA DO DIVIDENDO (P) - se for positivo, se for negativo 33 Uns
CHECK SE B � NEGATIVO OU NAO, SE FOR, NEGATIVA OS 2

----REPETE 32 VEZES
SHIFT LEFT 1 (P)
CHECA 1 BIT ESQUERDA P - SE FOR 1 -> SOMA COM A.      SE FOR 0 -> P - A
CHECA 1 BIT ESQUERDA P - SE FOR 0 -> O BIT DIREITA = 1.   

JOGA RESULTADO HI E LO
P - 63:32 VAI PRA HI
P - 31:0 VAI PRO LO
*/