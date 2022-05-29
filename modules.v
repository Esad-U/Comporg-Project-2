// Group 49
// Member Names: Yusuf Aslan, Ali Esad Uğur, Hasan Fatih Durkaya
// IDs: 150190098, 150200050, 150200074

`timescale 1ns / 1ps

module register16bit(I, E, CLK, FunSel, Q);
    input [15:0] I;
    input E;
    input CLK;
    input [1:0] FunSel;
    output reg [15:0] Q;
    
    always @ (posedge CLK) 
    begin
        if (E == 1)
        begin
            case(FunSel)
                2'b00   : Q <= Q - 16'd1; 
                2'b01   : Q <= Q + 16'd1; 
                2'b10   : Q <= I; 
                2'b11   : Q <= 16'd0;
                default : Q <= Q;
            endcase
        end
        else 
        begin
            Q <= Q;
        end
    end
endmodule

module register8bit(I, E, CLK, FunSel, Q);
    input [7:0] I;
    input E;
    input CLK;
    input [1:0] FunSel;
    output reg [7:0] Q;
    
    always @ (posedge CLK) 
    begin
        if (E == 1)
        begin
            case(FunSel)
                2'b00   : Q <= Q - 8'd1; 
                2'b01   : Q <= Q + 8'd1; 
                2'b10   : Q <= I; 
                2'b11   : Q <= 8'd0;
                default : Q <= Q;
            endcase
        end
        else 
        begin
            Q <= Q;
        end
    end
endmodule

module register_file(I, outASel, outBSel, FunSel, RegSel, CLK, outA, outB);
    input [7:0] I;
    input [1:0] outASel;
    input [1:0] outBSel;
    input [1:0] FunSel;
    input [3:0] RegSel;
    input CLK;
    
    output reg [7:0] outA;
    output reg [7:0] outB;
 
    wire [7:0] r1, r2, r3, r4;

    register8bit R1(I, ~RegSel[3], CLK, FunSel, r1);
    register8bit R2(I, ~RegSel[2], CLK, FunSel, r2);
    register8bit R3(I, ~RegSel[1], CLK, FunSel, r3);
    register8bit R4(I, ~RegSel[0], CLK, FunSel, r4);

    always @ (*) begin
        case(outASel)
            2'b00   : outA <= r1; 
            2'b01   : outA <= r2; 
            2'b10   : outA <= r3; 
            2'b11   : outA <= r4; 
        endcase
        
        case(outBSel)
            2'b00   : outB <= r1; 
            2'b01   : outB <= r2; 
            2'b10   : outB <= r3; 
            2'b11   : outB <= r4;
        endcase
    end 

endmodule

module address_register_file(I, outCSel, outDSel, FunSel, RegSel, CLK, outC, outD);
    input [7:0] I;
    input [1:0] outCSel;
    input [1:0] outDSel;
    input [1:0] FunSel;
    input [2:0] RegSel;
    input CLK;
    
    output reg [7:0] outC;
    output reg [7:0] outD;
 
    wire [7:0] PC_out, AR_out, SP_out;

    register8bit PC(I, ~RegSel[2], CLK, FunSel, PC_out);
    register8bit AR(I, ~RegSel[1], CLK, FunSel, AR_out);
    register8bit SP(I, ~RegSel[0], CLK, FunSel, SP_out);

    always @ (*) begin
        case(outCSel)
            2'b00   : outC <= PC_out; 
            2'b01   : outC <= PC_out; 
            2'b10   : outC <= AR_out; 
            2'b11   : outC <= SP_out;
        endcase
        
        case(outDSel)
            2'b00   : outD <= PC_out; 
            2'b01   : outD <= PC_out; 
            2'b10   : outD <= AR_out; 
            2'b11   : outD <= SP_out;
        endcase
    end 
    
    
endmodule

module IR_register(I, E, L_H, CLK, FunSel, IRout);
    input [7:0] I;
    input E;
    input CLK;
    input L_H;
    input [1:0] FunSel;
    output reg [15:0] IRout;
    
    wire [15:0] out;
    reg [15:0] concat;

    register16bit IR(concat, E, CLK, FunSel, out);
    
    always @ (*) begin
        IRout <= out;
        
        if (FunSel == 2'b10) begin
            if (L_H == 0) begin
                concat <= {I, IRout[7:0]};
            end
            else if (L_H == 1) begin
                concat <= {IRout[15:8], I};
            end
        end
    end
    
    
endmodule

module ALU(A, B, FunSel, clock, OutALU, OutFlag);
    input [7:0] A;
    input [7:0] B;
    input [3:0] FunSel;
    input clock;
    output reg [7:0] OutALU;
    output reg [3:0] OutFlag;
    
    reg [3:0] tempOutFlag;
    reg [7:0] tempOutAlu;
    
    always @ (*) begin
        if (FunSel == 4'b0000) begin
            OutALU = A;
            if (OutALU == 4'b0000) begin
                tempOutFlag[3] = 1'b1;
            end
            else begin 
                tempOutFlag[3] = 1'b0;
            end
            
            tempOutFlag[1] = OutALU[7];
        end
        
        if (FunSel == 4'b0001) begin
            OutALU = B;
            if (OutALU == 4'b0000) begin
                tempOutFlag[3] = 1'b1;
            end
            else begin 
                tempOutFlag[3] = 1'b0;
            end
            
            tempOutFlag[1] = OutALU[7];
        end
        
        if (FunSel == 4'b0010) begin
            OutALU = ~A;
            if (OutALU == 4'b0000) begin
                tempOutFlag[3] = 1'b1;
            end
            else begin 
                tempOutFlag[3] = 1'b0;
            end
        
            tempOutFlag[1] = OutALU[7];
        end
        
        if (FunSel == 4'b0011) begin
            OutALU = ~B;
            if (OutALU == 4'b0000) begin
                tempOutFlag[3] = 1'b1;
            end
            else begin 
                tempOutFlag[3] = 1'b0;
            end     
            
            tempOutFlag[1] = OutALU[7];
        end
        
        if (FunSel == 4'b0100) begin
            {tempOutFlag[2], OutALU} = A + B;
            if (OutALU == 4'b0000) begin
                tempOutFlag[3] = 1'b1;
            end
            else begin 
                tempOutFlag[3] = 1'b0;
            end

            tempOutFlag[1] = OutALU[7];
            tempOutFlag[0] = ~(A[7] ^ B[7]) & (A[7] ^ OutALU[7]);     
        end        
        
        if (FunSel == 4'b0101) begin
            {tempOutFlag[2], OutALU} = A + B + OutFlag[2];
            if (OutALU == 4'b0000) begin
                tempOutFlag[3] = 1'b1;
            end
            else begin 
                tempOutFlag[3] = 1'b0;
            end
    
            tempOutFlag[1] = OutALU[7];
            tempOutFlag[0] = ~(A[7] ^ B[7]) & (A[7] ^ OutALU[7]);     
        end
        
        if (FunSel == 4'b0110) begin
            {tempOutFlag[2], OutALU} = A - B;
            if (OutALU == 4'b0000) begin
                tempOutFlag[3] = 1'b1;
            end
            else begin 
                tempOutFlag[3] = 1'b0;
            end
    
            tempOutFlag[1] = OutALU[7];
            tempOutFlag[0] = (A[7] ^ B[7]) & (A[7] ^ OutALU[7]);     
        end

        if (FunSel == 4'b0111) begin
            OutALU = A & B;
            if (OutALU == 4'b0000) begin
                tempOutFlag[3] = 1'b1;
            end
            else begin 
                tempOutFlag[3] = 1'b0;
            end
        
            tempOutFlag[1] = OutALU[7];
        end

        if (FunSel == 4'b1000) begin
            OutALU = A | B;
            if (OutALU == 4'b0000) begin
                tempOutFlag[3] = 1'b1;
            end
            else begin 
                tempOutFlag[3] = 1'b0;
            end
        
            tempOutFlag[1] = OutALU[7];
        end
        
        if (FunSel == 4'b1001) begin
            OutALU = A ^ B;
            if (OutALU == 4'b0000) begin
                tempOutFlag[3] = 1'b1;
            end
            else begin 
                tempOutFlag[3] = 1'b0;
            end
        
            tempOutFlag[1] = OutALU[7];
        end 
        
        if (FunSel == 4'b1010) begin
            OutALU = {A[6:0], 1'b0};
            if (OutALU == 4'b0000) begin
                tempOutFlag[3] = 1'b1;
            end
            else begin 
                tempOutFlag[3] = 1'b0;
            end
            
            tempOutFlag[2] = A[7];
            tempOutFlag[1] = OutALU[7];
        end

        if (FunSel == 4'b1011) begin
            OutALU = {1'b0, A[7:1]};
            if (OutALU == 4'b0000) begin
                tempOutFlag[3] = 1'b1;
            end
            else begin 
                tempOutFlag[3] = 1'b0;
            end
            
            tempOutFlag[2] = A[0];
            tempOutFlag[1] = OutALU[7];

        end    
        
        if (FunSel == 4'b1100) begin
            OutALU = {A[6:0], 1'b0};
            if (OutALU == 4'b0000) begin
                tempOutFlag[3] = 1'b1;
            end
            else begin 
                tempOutFlag[3] = 1'b0;
            end

            tempOutFlag[0] = A[7] ^ A[6];
            tempOutFlag[1] = OutALU[7];
        end
        
        if (FunSel == 4'b1101) begin
            OutALU = {A[7], A[7:1]};
            if (OutALU == 4'b0000) begin
                tempOutFlag[3] = 1'b1;
            end
            else begin 
                tempOutFlag[3] = 1'b0;
            end
        end
        
        if (FunSel == 4'b1110) begin
            OutALU = {A[6:0], OutFlag[2]};
            if (OutALU == 4'b0000) begin
                tempOutFlag[3] = 1'b1;
            end
            else begin 
                tempOutFlag[3] = 1'b0;
            end
    
            tempOutFlag[0] = A[7] ^ A[6];
            tempOutFlag[1] = OutALU[7];
            tempOutFlag[2] = A[7];
        end

        if (FunSel == 4'b1111) begin
            OutALU = {OutFlag[2], A[7:1]};
            if (OutALU == 4'b0000) begin
                tempOutFlag[3] = 1'b1;
            end
            else begin 
                tempOutFlag[3] = 1'b0;
            end
    
            tempOutFlag[0] = A[7] ^ OutFlag[2];
            tempOutFlag[1] = OutALU[7];
            tempOutFlag[2] = A[0];
        end 
    end
    
    always @ (posedge clock) begin
        OutFlag = tempOutFlag;
    end
    
endmodule

//Please put it in your modules.v 
module Memory(
    input wire[7:0] address,
    input wire[7:0] data,
    input wire wr, //Read = 0, Write = 1
    input wire cs, //Chip is enable when cs = 0
    input wire clock,
    output reg[7:0] o // Output
);
    //Declaration o?f the RAM Area
    reg[7:0] RAM_DATA[0:255];
    //Read Ram data from the file
    initial $readmemh("./RAM.mem", RAM_DATA);
    //Read the selected data from RAM
    always @(*) begin
        o = ~wr && ~cs ? RAM_DATA[address] : 8'hZ;
    end
    
    //Write the data to RAM
    always @(posedge clock) begin
        if (wr && ~cs) begin
            RAM_DATA[address] <= data; 
        end
    end
endmodule

module ALUSystem(RF_OutASel, RF_OutBSel, RF_FunSel, RF_RegSel, ALU_FunSel,
                 ARF_OutCSel, ARF_OutDSel, ARF_FunSel, ARF_RegSel, IR_LH, IR_Enable,
                 IR_Funsel, Mem_WR, Mem_CS, MuxASel, MuxBSel, MuxCSel, Clock);
                 
    input [1:0] RF_OutASel; 
    input [1:0] RF_OutBSel; 
    input [1:0] RF_FunSel;
    input [3:0] RF_RegSel;
    input [3:0] ALU_FunSel;
    input [1:0] ARF_OutCSel; 
    input [1:0] ARF_OutDSel; 
    input [1:0] ARF_FunSel;
    input [2:0] ARF_RegSel;
    input       IR_LH;
    input       IR_Enable;
    input [1:0] IR_Funsel;
    input       Mem_WR;
    input       Mem_CS;
    input [1:0] MuxASel;
    input [1:0] MuxBSel;
    input       MuxCSel;
    input       Clock;
    
    reg [7:0] MuxAOut = 8'd0;
    reg [7:0] MuxBOut = 8'd0;
    reg [7:0] MuxCOut = 8'd0;
    wire [7:0] AOut;
    wire [7:0] BOut;
    wire [7:0] ARF_COut;
    wire [7:0] Address;
    wire [7:0] ALUOut;
    wire [3:0] ALUOutFlag;
    wire [7:0] MemoryOut;
    wire [15:0] IROut;   
    
    register_file RF(MuxAOut, RF_OutASel, RF_OutBSel, RF_FunSel, RF_RegSel, Clock, AOut, BOut);
    ALU ALU1(MuxCOut, BOut, ALU_FunSel, Clock, ALUOut, ALUOutFlag);
    address_register_file ARF(MuxBOut, ARF_OutCSel, ARF_OutDSel, ARF_FunSel, ARF_RegSel, Clock, ARF_COut, Address);
    IR_register IR(MemoryOut, IR_Enable, IR_LH, Clock, IR_Funsel, IROut);
    Memory MEM(Address, ALUOut, Mem_WR, Mem_CS, Clock, MemoryOut);

    always @(*) begin
        case(MuxASel)
            2'b00   : MuxAOut = IROut[7:0]; 
            2'b01   : MuxAOut = MemoryOut; 
            2'b10   : MuxAOut = ARF_COut; 
            2'b11   : MuxAOut = ALUOut;
        endcase
        
        case(MuxBSel)
            2'b00   : MuxBOut = MuxBOut; 
            2'b01   : MuxBOut = IROut[7:0]; 
            2'b10   : MuxBOut = MemoryOut; 
            2'b11   : MuxBOut = ALUOut;
        endcase
        
        case(MuxCSel)
            1'b0    : MuxCOut = ARF_COut;
            1'b1    : MuxCOut = AOut;
        endcase
    end
    
endmodule


module CompleteSystem(clock);
    input       clock;
    reg [1:0]   RF_OutASel; 
    reg [1:0]   RF_OutBSel; 
    reg [1:0]   RF_FunSel;
    reg [3:0]   RF_RegSel;
    reg [3:0]   ALU_FunSel;
    reg [1:0]   ARF_OutCSel; 
    reg [1:0]   ARF_OutDSel; 
    reg [1:0]   ARF_FunSel;
    reg [2:0]   ARF_RegSel;
    reg         IR_LH;
    reg         IR_Enable;
    reg [1:0]   IR_Funsel;
    reg         Mem_WR; //Read = 0, Write = 1
    reg         Mem_CS; //Chip is enable when cs = 0
    reg [1:0]   MuxASel;
    reg [1:0]   MuxBSel;
    reg         MuxCSel;
    reg [2:0]   T = 3'b000;
    
    reg REGSEL;

    reg [3:0] DEST_REG;
    reg [3:0] SRCREG1;
    reg [3:0] SRCREG2;

    ALUSystem aluSystem(.RF_OutASel(RF_OutASel), 
    .RF_OutBSel(RF_OutBSel), 
    .RF_FunSel(RF_FunSel),
    .RF_RegSel(RF_RegSel),
    .ALU_FunSel(ALU_FunSel),
    .ARF_OutCSel(ARF_OutCSel), 
    .ARF_OutDSel(ARF_OutDSel), 
    .ARF_FunSel(ARF_FunSel),
    .ARF_RegSel(ARF_RegSel),
    .IR_LH(IR_LH),
    .IR_Enable(IR_Enable),
    .IR_Funsel(IR_Funsel),
    .Mem_WR(Mem_WR),
    .Mem_CS(Mem_CS),
    .MuxASel(MuxASel),
    .MuxBSel(MuxBSel),
    .MuxCSel(MuxCSel),
    .Clock(clock));
    
        
    always @(posedge clock) begin
        // fetching LSB
        if(T == 3'b000) begin
            RF_RegSel <= 4'b1111;
            ARF_OutDSel <= 2'b00;
            ARF_FunSel <= 2'b01;
            ARF_RegSel <= 3'b011;
            IR_LH <= 1'b1;
            IR_Enable <= 1'b1;
            IR_Funsel <= 2'b10;
            Mem_WR <= 1'b0;
            Mem_CS <= 1'b0;
            T <= T + 1;
        end
        // fetching MSB
        else if(T == 3'b001) begin
            RF_RegSel <= 4'b1111;
            ARF_OutDSel <= 2'b00;
            ARF_FunSel <= 2'b01;
            ARF_RegSel <= 3'b011;
            IR_LH <= 1'b0;
            IR_Enable <= 1'b1;
            IR_Funsel <= 2'b10;
            Mem_WR <= 1'b0;
            Mem_CS <= 1'b0;
            T <= T + 1;
        end
        // decoding
        else if(T == 2) begin
            case(aluSystem.IROut[15:12])
            0000: begin
                if (aluSystem.IROut[10] == 1) begin
                    MuxBSel <= 2'b01;
                    ARF_RegSel <= 3'b011; 
                    ARF_FunSel <= 2'b10;
                    Mem_CS <= 1'b1;
                    IR_Enable <= 1'b0;
                    RF_RegSel <= 4'b1111;
                    T <= 3'b000;  
                end
            end
            0001: begin
                if (aluSystem.IROut[10] == 1) begin
                    MuxASel <= 2'b00;
                    ARF_RegSel <= 3'b111;
                    if (aluSystem.IROut[9:8] == 2'b00) begin
                        RF_RegSel <= 4'b0111;
                    end else if (aluSystem.IROut[9:8] == 2'b01) begin
                        RF_RegSel <= 4'b1011;
                    end else if (aluSystem.IROut[9:8] == 2'b10) begin
                        RF_RegSel <= 4'b1101;
                    end else if (aluSystem.IROut[9:8] == 2'b11) begin
                        RF_RegSel <= 4'b1110;
                    end
                    RF_FunSel <= 2'b10;
                    Mem_CS <= 1'b1;
                    IR_Enable <= 1'b0;
                    T <= 3'b000;  
                end else if (aluSystem.IROut[10] == 0) begin
                    MuxBSel <= 2'b01;
                    ARF_RegSel <= 3'b101;
                    ARF_FunSel <= 2'b10;
                    ARF_OutDSel <= 2'b10;
                    Mem_CS <= 1'b1;
                    IR_Enable <= 1'b0;
                    RF_RegSel <= 4'b1111;
                    T <= T + 1;
                end
            end
            0010: begin
                if (aluSystem.IROut[10] == 0) begin
                    MuxBSel <= 2'b01;
                    ARF_RegSel <= 3'b101;
                    ARF_FunSel <= 2'b10;
                    ARF_OutDSel <= 2'b10;
                    Mem_CS <= 1'b1;
                    IR_Enable <= 1'b0;
                    RF_RegSel <= 4'b1111;
                    T <= T + 1;
                end
            end
            0011: begin
                Mem_CS <= 1'b1;
                IR_Enable <= 1'b0;
                case(aluSystem.IROut[7:4])
                0000, 0001: begin
                    ARF_OutCSel <= 2'b00;
                    case(aluSystem.IROut[11:8])
                    0010: begin
                        MuxCSel <= 1'b0;
                        ALU_FunSel <= 4'b0000;
                        MuxBSel <= 2'b11;
                        ARF_RegSel <= 3'b101;
                        ARF_FunSel <= 2'b10;
                    end
                    0011: begin
                        MuxCSel <= 1'b0;
                        ALU_FunSel <= 4'b0000;
                        MuxBSel <= 2'b11;
                        ARF_RegSel <= 3'b110;
                        ARF_FunSel <= 2'b10;
                    end
                    0100: begin
                        MuxASel <= 2'b10;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b0111;
                    end
                    0101: begin
                        MuxASel <= 2'b10;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1011;
                    end
                    0110: begin
                        MuxASel <= 2'b10;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1101;
                    end
                    0111: begin
                        MuxASel <= 2'b10;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1110;
                    end
                    endcase
                    T <= 3'b000;
                end
                0010: begin
                    ARF_OutCSel <= 2'b10;
                    case(aluSystem.IROut[11:8])
                    0000, 0001: begin
                        MuxCSel <= 1'b0;
                        ALU_FunSel <= 4'b0000;
                        MuxBSel <= 2'b11;
                        ARF_RegSel <= 3'b011;
                        ARF_FunSel <= 2'b10;
                    end
                    0011: begin
                        MuxCSel <= 1'b0;
                        ALU_FunSel <= 4'b0000;
                        MuxBSel <= 2'b11;
                        ARF_RegSel <= 3'b110;
                        ARF_FunSel <= 2'b10;
                    end
                    0100: begin
                        MuxASel <= 2'b10;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b0111;
                    end
                    0101: begin
                        MuxASel <= 2'b10;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1011;
                    end
                    0110: begin
                        MuxASel <= 2'b10;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1101;
                    end
                    0111: begin
                        MuxASel <= 2'b10;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1110;
                    end
                    endcase
                    T <= 3'b000;
                end
                0011: begin
                    ARF_OutCSel <= 2'b11;
                    case(aluSystem.IROut[11:8])
                    0000, 0001: begin
                        MuxCSel <= 1'b0;
                        ALU_FunSel <= 4'b0000;
                        MuxBSel <= 2'b11;
                        ARF_RegSel <= 3'b011;
                        ARF_FunSel <= 2'b10;
                    end
                    0010: begin
                        MuxCSel <= 1'b0;
                        ALU_FunSel <= 4'b0000;
                        MuxBSel <= 2'b11;
                        ARF_RegSel <= 3'b101;
                        ARF_FunSel <= 2'b10;
                    end
                    0100: begin
                        MuxASel <= 2'b10;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b0111;
                    end
                    0101: begin
                        MuxASel <= 2'b10;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1011;
                    end
                    0110: begin
                        MuxASel <= 2'b10;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1101;
                    end
                    0111: begin
                        MuxASel <= 2'b10;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1110;
                    end
                    endcase
                    T <= 3'b000;
                end
                0100: begin
                    RF_OutBSel <= 2'b00;
                    ALU_FunSel <= 4'b0001;
                    case(aluSystem.IROut[11:8])
                    0000, 0001: begin
                        MuxBSel <= 2'b11;
                        ARF_FunSel <= 2'b10;
                        ARF_RegSel <= 3'b011;
                    end
                    0010: begin
                        MuxBSel <= 2'b11;
                        ARF_FunSel <= 2'b10;
                        ARF_RegSel <= 3'b101;
                    end
                    0011: begin
                        MuxBSel <= 2'b11;
                        ARF_FunSel <= 2'b10;
                        ARF_RegSel <= 3'b110;
                    end
                    0101: begin
                        MuxASel <= 2'b11;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1011;
                    end
                    0110: begin
                        MuxASel <= 2'b11;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1101;
                    end
                    0111: begin
                        MuxASel <= 2'b11;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1110;
                    end
                    endcase
                    T <= 3'b000;
                end
                0101: begin
                    RF_OutBSel <= 2'b01;
                    ALU_FunSel <= 4'b0001;
                    case(aluSystem.IROut[11:8])
                    0000, 0001: begin
                        MuxBSel <= 2'b11;
                        ARF_FunSel <= 2'b10;
                        ARF_RegSel <= 3'b011;
                    end
                    0010: begin
                        MuxBSel <= 2'b11;
                        ARF_FunSel <= 2'b10;
                        ARF_RegSel <= 3'b101;
                    end
                    0011: begin
                        MuxBSel <= 2'b11;
                        ARF_FunSel <= 2'b10;
                        ARF_RegSel <= 3'b110;
                    end
                    0100: begin
                        MuxASel <= 2'b11;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b0111;
                    end
                    0110: begin
                        MuxASel <= 2'b11;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1101;
                    end
                    0111: begin
                        MuxASel <= 2'b11;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1110;
                    end
                    endcase
                    T <= 3'b000;
                end
                0110: begin
                    RF_OutBSel <= 2'b10;
                    ALU_FunSel <= 4'b0001;
                    case(aluSystem.IROut[11:8])
                    0000, 0001: begin
                        MuxBSel <= 2'b11;
                        ARF_FunSel <= 2'b10;
                        ARF_RegSel <= 3'b011;
                    end
                    0010: begin
                        MuxBSel <= 2'b11;
                        ARF_FunSel <= 2'b10;
                        ARF_RegSel <= 3'b101;
                    end
                    0011: begin
                        MuxBSel <= 2'b11;
                        ARF_FunSel <= 2'b10;
                        ARF_RegSel <= 3'b110;
                    end
                    0100: begin
                        MuxASel <= 2'b11;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b0111;
                    end
                    0101: begin
                        MuxASel <= 2'b11;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1011;
                    end
                    0111: begin
                        MuxASel <= 2'b11;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1110;
                    end
                    endcase
                    T <= 3'b000;
                end
                0111: begin
                    RF_OutBSel <= 2'b11;
                    ALU_FunSel <= 4'b0001;
                    case(aluSystem.IROut[11:8])
                    0000, 0001: begin
                        MuxBSel <= 2'b11;
                        ARF_FunSel <= 2'b10;
                        ARF_RegSel <= 3'b011;
                    end
                    0010: begin
                        MuxBSel <= 2'b11;
                        ARF_FunSel <= 2'b10;
                        ARF_RegSel <= 3'b101;
                    end
                    0011: begin
                        MuxBSel <= 2'b11;
                        ARF_FunSel <= 2'b10;
                        ARF_RegSel <= 3'b110;
                    end
                    0100: begin
                        MuxASel <= 2'b11;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b0111;
                    end
                    0101: begin
                        MuxASel <= 2'b11;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1011;
                    end
                    0110: begin
                        MuxASel <= 2'b11;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1101;
                    end
                    endcase
                    T <= 3'b000;
                end
                endcase
            end
            0100, 0101: begin
                Mem_CS <= 1'b1;
                IR_Enable <= 1'b0;
                case(aluSystem.IROut[7:4]) // SRC1
                0000, 0001: begin
                    ARF_OutCSel <= 2'b00;
                    MuxASel <= 2'b10;
                    RF_FunSel <= 2'b10;
                    if(aluSystem.IROut[3:0] != 4'b0111 && aluSystem.IROut[11:8] != 4'b0111) begin
                        RF_RegSel <= 4'b1110;
                        RF_OutBSel <= 2'b11;
                    end else begin
                        RF_RegSel <= 4'b0111;
                        RF_OutBSel <= 2'b00;
                    end
                end
                0010: begin
                    ARF_OutCSel <= 2'b10;
                    MuxASel <= 2'b10;
                    RF_FunSel <= 2'b10;
                    if(aluSystem.IROut[3:0] != 4'b0111 && aluSystem.IROut[11:8] != 4'b0111) begin
                        RF_RegSel <= 4'b1110;
                        RF_OutBSel <= 2'b11;
                    end else begin
                        RF_RegSel <= 4'b0111;
                        RF_OutBSel <= 2'b00;
                    end
                end
                0011: begin
                    ARF_OutCSel <= 2'b11;
                    MuxASel <= 2'b10;
                    RF_FunSel <= 2'b10;
                    if(aluSystem.IROut[3:0] != 4'b0111 && aluSystem.IROut[11:8] != 4'b0111) begin
                        RF_RegSel <= 4'b1110;
                        RF_OutBSel <= 2'b11;
                    end else begin
                        RF_RegSel <= 4'b0111;
                        RF_OutBSel <= 2'b00;
                    end
                end
                0100: begin
                    RF_OutBSel <= 2'b00;
                    MuxCSel <= 1'b1;
                end
                0101: begin
                    RF_OutBSel <= 2'b01;
                    MuxCSel <= 1'b1;
                end
                0110: begin
                    RF_OutBSel <= 2'b10;
                    MuxCSel <= 1'b1;
                end
                0111: begin
                    RF_OutBSel <= 2'b11;
                    MuxCSel <= 1'b1;
                end
                endcase
                T <= T + 1;
            end
            
            0110: begin
                Mem_CS <= 1'b1;
                IR_Enable  <= 1'b0;
                case(aluSystem.IROut[7:4])
                    0000,0001: begin
                        ARF_OutCSel <= 2'b00;
                        case(aluSystem.IROut[11:8])
                            0000,0001:begin
                                MuxCSel <= 1'b0;
                                ALU_FunSel <= 4'b0010;
                                MuxBSel <= 2'b11;
                                ARF_RegSel <= 3'b011;
                                ARF_FunSel <= 2'b10;
                            end
                            0010:begin
                                MuxCSel <= 1'b0;
                                ALU_FunSel <= 4'b0010;
                                MuxBSel <= 2'b11;
                                ARF_RegSel <= 3'b101;
                                ARF_FunSel <= 2'b10;
                            end
                            0011:begin
                                MuxCSel <= 1'b0;
                                ALU_FunSel <= 4'b0010;
                                MuxBSel <= 2'b11;
                                ARF_RegSel <= 3'b110;
                                ARF_FunSel <= 2'b10;                                
                            end
                            0100:begin
                                MuxCSel <= 1'b0;
                                ALU_FunSel <= 4'0010;
                                MuxASel <= 2'b11;                                
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b0111;
                            end
                            0101:begin
                                MuxCSel <= 1'b0;
                                ALU_FunSel <= 4'b0010;
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1011;
                            end
                            0110:begin
                                MuxCSel <= 1'b0;
                                ALU_FunSel <= 4'b0010;
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1101;
                            end
                            0111:begin
                                MuxCSel <= 1'b0;
                                MuxASel <= 2'b10;
                                ALU_FunSel <= 4'b0010;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1110;
                            end

                        endcase
                        T <= 3'b000;
                    end
                    0010:begin
                        ARF_OutCSel <= 2'b10;
                        case(ALUSystem.IROut[11:8])
                            0000,0001:begin
                                MuxCSel <= 1'b0;
                                ALU_FunSel <= 4'b0010;
                                MuxBSel <= 2'b11;
                                ARF_RegSel <= 3'b011;
                                ARF_FunSel <= 2'b10;
                            end
                            0010:begin
                                MuxCSel <= 1'b0;
                                ALU_FunSel <= 4'b0010;
                                MuxBSel <= 2'b11;
                                ARF_RegSel <= 3'b101;
                                ARF_FunSel <= 2'b10;
                            end
                            0011:begin
                                MuxCSel <= 1'b0;
                                ALU_FunSel <= 4'b0010;
                                MuxBSel <= 2'b11;
                                ARF_RegSel <= 3'b110;
                                ARF_FunSel <= 2'b10;                                
                            end
                            0100:begin
                                MuxCSel <= 1'b0;
                                ALU_FunSel <= 4'0010;
                                MuxASel <= 2'b11;                                
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b0111;
                            end
                            0101:begin
                                MuxCSel <= 1'b0;
                                ALU_FunSel <= 4'b0010;
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1011;
                            end
                            0110:begin
                                MuxCSel <= 1'b0;
                                ALU_FunSel <= 4'b0010;
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1101;
                            end
                            0111:begin
                                MuxCSel <= 1'b0;
                                ALU_FunSel <= 4'b0010;
                                MuxASel <= 2'b10;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1110;
                            end

                        endcase
                        T <=3'b000;
                    end
                    0011:begin
                        ARF_OutCSel <= 2'b11;
                        case(ALUSystem.IROut[11:8])
                            0000,0001:begin
                                MuxCSel <= 1'b0;
                                ALU_FunSel <= 4'b0010;
                                MuxBSel <= 2'b11;
                                ARF_RegSel <= 3'b011;
                                ARF_FunSel <= 2'b10;
                            end
                            0010:begin
                                MuxCSel <= 1'b0;
                                ALU_FunSel <= 4'b0010;
                                MuxBSel <= 2'b11;
                                ARF_RegSel <= 3'b101;
                                ARF_FunSel <= 2'b10;
                            end
                            0011:begin
                                MuxCSel <= 1'b0;
                                ALU_FunSel <= 4'b0010;
                                MuxBSel <= 2'b11;
                                ARF_RegSel <= 3'b110;
                                ARF_FunSel <= 2'b10;                                
                            end
                            0100:begin
                                MuxCSel <= 1'b0;
                                ALU_FunSel <= 4'0010;
                                MuxASel <= 2'b11;                                
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b0111;
                            end
                            0101:begin
                                MuxCSel <= 1'b0;
                                ALU_FunSel <= 4'b0010;
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1011;
                            end
                            0110:begin
                                MuxCSel <= 1'b0;
                                ALU_FunSel <= 4'b0010;
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1101;
                            end
                            0111:begin
                                MuxCSel <= 1'b0;
                                ALU_FunSel <= 4'b0010;
                                MuxASel <= 2'b10;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1110;
                            end

                        endcase
                        T <=3'b000;
                    end
                    0100:begin
                        RF_OutBSel <= 2'b00;
                        ALU_FunSel <= 4'b0011;
                        case(ALUSystem.IROut[11:8])
                            0000,0001:begin
                                MuxBSel <= 2'b11;
                                ARF_FunSel <= 2'b10;
                                ARF_RegSel <= 3'b011;                        
                            end
                            0010:begin
                                MuxBSel <= 2'b11;
                                ARF_FunSel <= 2'b10;
                                ARF_RegSel <= 3'b101;
                            end
                            0011:begin
                                MuxBSel <= 2'b11;
                                ARF_FunSel <= 2'b10;
                                ARF_RegSel <= 3'b110;                    
                            end
                            0100:begin
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b0111;
                            end
                            0101:begin
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1011;                        
                            end
                            0110:begin
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1101;                    
                            end
                            0111:begin
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1110;                        
                            end
                        endcase
                        T <=3'b000;
                    end
                    0101:begin
                        RF_OutBSel <= 2'b01;
                        ALU_FunSel <= 4'b0011;
                        case(ALUSystem.IROut[11:8])
                            0000,0001:begin
                                MuxBSel <= 2'b11;
                                ARF_FunSel <= 2'b10;
                                ARF_RegSel <= 3'b011;                        
                            end
                            0010:begin
                                MuxBSel <= 2'b11;
                                ARF_FunSel <= 2'b10;
                                ARF_RegSel <= 3'b101;                    
                            end
                            0011:begin
                                MuxBSel <= 2'b11;
                                ARF_FunSel <= 2'b10;
                                ARF_RegSel <= 3'b110;                    
                            end
                            0100:begin
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b0111;                    
                            end
                            0101:begin
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1011;
                            end
                            0110:begin
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1101;                    
                            end
                            0111:begin
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1110;                    
                            end
                        endcase
                        T <=3'b000;
                    end
                    0110:begin
                            RF_OutBSel <= 2'b10;
                            ALU_FunSel <= 4'b0011;
                        case(ALUSystem.IROut[11:8])
                            0000,0001:begin
                                MuxBSel <= 2'b11;
                                ARF_FunSel <= 2'b10;
                                ARF_RegSel <= 3'b011;                        
                            end
                            0010:begin
                                MuxBSel <= 2'b11;
                                ARF_FunSel <= 2'b10;
                                ARF_RegSel <= 3'b101;                         
                            end
                            0011:begin
                                MuxBSel <= 2'b11;
                                ARF_FunSel <= 2'b10;
                                ARF_RegSel <= 3'b110;                    
                            end
                            0100:begin
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b0111;                    
                            end
                            0101:begin
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1011;                    
                            end
                            0110:begin
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1101;
                            end
                            0111:begin
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1110;                    
                            end
                        endcase
                        T <=3'b000;
                    end
                    0111:begin
                            RF_OutBSel <= 2'b11;
                            ALU_FunSel <= 4'b0011;
                        case(ALUSystem.IROut[11:8])
                            0000,0001:begin
                                MuxBSel <= 2'b11;
                                ARF_FunSel <= 2'b10;
                                ARF_RegSel <= 3'b011;                        
                            end
                            0010:begin
                                MuxBSel <= 2'b11;
                                ARF_FunSel <= 2'b10;
                                ARF_RegSel <= 3'b101;                    
                            end
                            0011:begin
                                MuxBSel <= 2'b11;
                                ARF_FunSel <= 2'b10;
                                ARF_RegSel <= 3'b110;                    
                            end
                            0100:begin
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b0111;                    
                            end
                            0101:begin
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1011;                    
                            end
                            0110:begin
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1101;                    
                            end
                            0111:begin
                                MuxASel <= 2'b11;
                                RF_FunSel <= 2'b10;
                                RF_RegSel <= 4'b1110;
                            end
                        endcase
                        T <=3'b000;
                    end                    
                endcase
            end

            0111, 1000:begin
                Mem_CS <= 1'b1;
                IR_Enable <= 1'b0;
                case(ALUSystem.IROut[7:4])
                    0000, 0001: begin
                        ARF_OutCSel <= 2'b00;
                        MuxASel <= 2'b10;
                        RF_FunSel <= 2'b10;
                        if(aluSystem.IROut[3:0] != 4'b0111 && aluSystem.IROut[11:8] != 4'b0111) begin
                            RF_RegSel <= 4'b1110;
                            RF_OutBSel <= 2'b11;
                        end 
                        else begin
                            RF_RegSel <= 4'b0111;
                            RF_OutBSel <= 2'b00;
                        end    
                    end
                    0010:begin
                        ARF_OutCSel <= 2'b10;
                        MuxASel <= 2'b10;
                        RF_FunSel <= 2'b10;
                        if(aluSystem.IROut[3:0] != 4'b0111 && aluSystem.IROut[11:8] != 4'b0111) begin
                            RF_RegSel <= 4'b1110;
                            RF_OutBSel <= 2'b11;
                        end else begin
                            RF_RegSel <= 4'b0111;
                            RF_OutBSel <= 2'b00;
                        end                    
                    end
                    0011:begin
                        ARF_OutCSel <= 2'b11;
                        MuxASel <= 2'b10;
                        RF_FunSel <= 2'b10;
                        if(aluSystem.IROut[3:0] != 4'b0111 && aluSystem.IROut[11:8] != 4'b0111) begin
                            RF_RegSel <= 4'b1110;
                            RF_OutBSel <= 2'b11;
                        end else begin
                            RF_RegSel <= 4'b0111;
                            RF_OutBSel <= 2'b00;
                        end                
                    end
                    0100:begin
                        RF_OutBSel <= 2'b00;
                        MuxCSel <= 1'b1;            
                    end
                    0101:begin
                        RF_OutBSel <= 2'b01;
                        MuxCSel <= 1'b1;                
                    end
                    0110:begin
                        RF_OutBSel <= 2'b10;
                        MuxCSel <= 1'b1;                
                    end
                    0111:begin
                        RF_OutBSel <= 2'b11;
                        MuxCSel <= 1'b1;                
                    end
                endcase
                T <= T + 1;
            end
            1010:begin
                Mem_CS <= 1'b1;
                IR_Enable <= 1'b0;
                case(aluSystem.IROut[7:4])
                    0000,0001:begin
                        ARF_OutCSel <= 2'b00;
                        case(aluSystem.IROut[11:8])
                        0010:begin
                            MuxCSel <= 1'b0;
                            ALU_FunSel <= 4'b1010;
                            MuxBSel <= 2'b11;
                            ARF_RegSel <= 3'b101;
                            ARF_FunSel <= 2'b10;
                        end
                        0011:begin
                            MuxCSel <= 1'b0;
                            ALU_FunSel <= 4'b1010;
                            MuxBSel <= 2'b11;
                            ARF_RegSel <= 3'b110;
                            ARF_FunSel <= 2'b10;                
                        end
                        0100:begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1010;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b0111;
                        end
                        0101:begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1010;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1011;
                        end
                        0110:begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1010;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1101;
                        end
                        0111:begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1010;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1110;
                        end                                                        
                        endcase
                        T <= 3'b000;    
                    end
                    0010:begin
                        ARF_OutCSel <= 2'b10;
                        case(aluSystem.IROut[11:8])
                        0000, 0001: begin
                            MuxCSel <= 1'b0;
                            ALU_FunSel <= 4'b1010;
                            MuxBSel <= 2'b11;
                            ARF_RegSel <= 3'b011;
                            ARF_FunSel <= 2'b10;
                        end
                        0011: begin
                            MuxCSel <= 1'b0;
                            ALU_FunSel <= 4'b1010;
                            MuxBSel <= 2'b11;
                            ARF_RegSel <= 3'b110;
                            ARF_FunSel <= 2'b10;
                        end
                        0100: begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1010;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b0111;
                        end
                        0101: begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1010;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1011;
                        end
                        0110: begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1010;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1101;
                        end
                        0111: begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1010;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1110;
                        end                                                                                    
                        endcase
                        T <= 3'b000;
                    end
                    0011: begin
                        ARF_OutCSel <= 2'b11;
                        case(aluSystem.IROut[11:8])
                        0000, 0001: begin
                            MuxCSel <= 1'b0;
                            ALU_FunSel <= 4'b1010;
                            MuxBSel <= 2'b11;
                            ARF_RegSel <= 3'b011;
                            ARF_FunSel <= 2'b10;
                        end
                        0010: begin
                            MuxCSel <= 1'b0;
                            ALU_FunSel <= 4'b1010;
                            MuxBSel <= 2'b11;
                            ARF_RegSel <= 3'b101;
                            ARF_FunSel <= 2'b10;
                        end
                        0100: begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1010;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b0111;
                        end
                        0101: begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1010;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1011;
                        end
                        0110: begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1010;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1101;
                        end
                        0111: begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1010;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1110;
                        end
                        endcase
                        T <= 3'b000;
                    end
                    0100: begin
                        RF_OutBSel <= 2'b00;
                        ALU_FunSel <= 4'b1010;
                        case(aluSystem.IROut[11:8])
                        0000, 0001: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b011;
                        end
                        0010: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b101;
                        end
                        0011: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b110;
                        end
                        0101: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1011;
                        end
                        0110: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1101;
                        end
                        0111: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1110;
                        end
                        endcase
                        T <= 3'b000;
                    end
                    0101: begin
                        RF_OutBSel <= 2'b01;
                        ALU_FunSel <= 4'b1010;
                        case(aluSystem.IROut[11:8])
                        0000, 0001: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b011;
                        end
                        0010: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b101;
                        end
                        0011: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b110;
                        end
                        0100: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b0111;
                        end
                        0110: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1101;
                        end
                        0111: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1110;
                        end
                        endcase
                        T <= 3'b000;
                    end
                    0110: begin
                        RF_OutBSel <= 2'b10;
                        ALU_FunSel <= 4'b1010;
                        case(aluSystem.IROut[11:8])
                        0000, 0001: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b011;
                        end
                        0010: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b101;
                        end
                        0011: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b110;
                        end
                        0100: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b0111;
                        end
                        0101: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1011;
                        end
                        0111: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1110;
                        end
                        endcase
                        T <= 3'b000;
                    end
                    0111: begin
                        RF_OutBSel <= 2'b11;
                        ALU_FunSel <= 4'b1010;
                        case(aluSystem.IROut[11:8])
                        0000, 0001: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b011;
                        end
                        0010: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b101;
                        end
                        0011: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b110;
                        end
                        0100: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b0111;
                        end
                        0101: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1011;
                        end
                        0110: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1101;
                        end
                        endcase
                        T <= 3'b000;
                    end                                    
                endcase
            end
            1001:begin
                Mem_CS <= 1'b1;
                IR_Enable <= 1'b0;
                case(aluSystem.IROut[7:4])
                    0000,0001:begin
                        ARF_OutCSel <= 2'b00;
                        case(aluSystem.IROut[11:8])
                        0010:begin
                            MuxCSel <= 1'b0;
                            ALU_FunSel <= 4'b1011;
                            MuxBSel <= 2'b11;
                            ARF_RegSel <= 3'b101;
                            ARF_FunSel <= 2'b10;
                        end
                        0011:begin
                            MuxCSel <= 1'b0;
                            ALU_FunSel <= 4'b1011;
                            MuxBSel <= 2'b11;
                            ARF_RegSel <= 3'b110;
                            ARF_FunSel <= 2'b10;                
                        end
                        0100:begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1011;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b0111;
                        end
                        0101:begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1011;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1011;
                        end
                        0110:begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1011;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1101;
                        end
                        0111:begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1011;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1110;
                        end                                                        
                        endcase
                        T <= 3'b000;    
                    end
                    0010:begin
                        ARF_OutCSel <= 2'b10;
                        case(aluSystem.IROut[11:8])
                        0000, 0001: begin
                            MuxCSel <= 1'b0;
                            ALU_FunSel <= 4'b1011;
                            MuxBSel <= 2'b11;
                            ARF_RegSel <= 3'b011;
                            ARF_FunSel <= 2'b10;
                        end
                        0011: begin
                            MuxCSel <= 1'b0;
                            ALU_FunSel <= 4'b1011;
                            MuxBSel <= 2'b11;
                            ARF_RegSel <= 3'b110;
                            ARF_FunSel <= 2'b10;
                        end
                        0100: begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1011;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b0111;
                        end
                        0101: begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1011;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1011;
                        end
                        0110: begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1011;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1101;
                        end
                        0111: begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1011;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1110;
                        end                                                                                    
                        endcase
                        T <= 3'b000;
                    end
                    0011: begin
                        ARF_OutCSel <= 2'b11;
                        case(aluSystem.IROut[11:8])
                        0000, 0001: begin
                            MuxCSel <= 1'b0;
                            ALU_FunSel <= 4'b1011;
                            MuxBSel <= 2'b11;
                            ARF_RegSel <= 3'b011;
                            ARF_FunSel <= 2'b10;
                        end
                        0010: begin
                            MuxCSel <= 1'b0;
                            ALU_FunSel <= 4'b1011;
                            MuxBSel <= 2'b11;
                            ARF_RegSel <= 3'b101;
                            ARF_FunSel <= 2'b10;
                        end
                        0100: begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1011;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b0111;
                        end
                        0101: begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1011;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1011;
                        end
                        0110: begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1011;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1101;
                        end
                        0111: begin
                            MuxASel <= 2'b10;
                            ALU_FunSel <= 4'b1011;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1110;
                        end
                        endcase
                        T <= 3'b000;
                    end
                    0100: begin
                        RF_OutBSel <= 2'b00;
                        ALU_FunSel <= 4'b1011;
                        case(aluSystem.IROut[11:8])
                        0000, 0001: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b011;
                        end
                        0010: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b101;
                        end
                        0011: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b110;
                        end
                        0101: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1011;
                        end
                        0110: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1101;
                        end
                        0111: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1110;
                        end
                        endcase
                        T <= 3'b000;
                    end
                    0101: begin
                        RF_OutBSel <= 2'b01;
                        ALU_FunSel <= 4'b1011;
                        case(aluSystem.IROut[11:8])
                        0000, 0001: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b011;
                        end
                        0010: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b101;
                        end
                        0011: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b110;
                        end
                        0100: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b0111;
                        end
                        0110: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1101;
                        end
                        0111: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1110;
                        end
                        endcase
                        T <= 3'b000;
                    end
                    0110: begin
                        RF_OutBSel <= 2'b10;
                        ALU_FunSel <= 4'b1011;
                        case(aluSystem.IROut[11:8])
                        0000, 0001: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b011;
                        end
                        0010: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b101;
                        end
                        0011: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b110;
                        end
                        0100: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b0111;
                        end
                        0101: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1011;
                        end
                        0111: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1110;
                        end
                        endcase
                        T <= 3'b000;
                    end
                    0111: begin
                        RF_OutBSel <= 2'b11;
                        ALU_FunSel <= 4'b1011;
                        case(aluSystem.IROut[11:8])
                        0000, 0001: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b011;
                        end
                        0010: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b101;
                        end
                        0011: begin
                            MuxBSel <= 2'b11;
                            ARF_FunSel <= 2'b10;
                            ARF_RegSel <= 3'b110;
                        end
                        0100: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b0111;
                        end
                        0101: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1011;
                        end
                        0110: begin
                            MuxASel <= 2'b11;
                            RF_FunSel <= 2'b10;
                            RF_RegSel <= 4'b1101;
                        end
                        endcase
                        T <= 3'b000;
                    end                                    
                endcase
            end
            1011: begin             //pul
                Mem_WR <= 1'b1;
                Mem_CS <= 1'b0;
                ARF_RegSel <= 3'b111;
                ARF_OutDSel <= 2'b11;
                MuxASel <= 2'b01;
                IR_Enable <= 1'b0;
                RF_FunSel <= 2'b10;
                case(aluSystem.IROut[9:8])
                    2'b00: RF_RegSel <= 4'b0111;
                    2'b01: RF_RegSel <= 4'b1011;
                    2'b10: RF_RegSel <= 4'b1101;
                    2'b11: RF_RegSel <= 4'b1110;
                endcase
                T <= T + 1;
            end
            1100: ; //psh
            1101: ;
            1110: ;
            1111: begin
               if (aluSystem.ALUOutFlag[3] == 0 && aluSystem.IROut[10] == 1) begin
                   MuxBSel <= 2'b01;
                   ARF_RegSel <= 3'b011; 
                   ARF_FunSel <= 2'b10;
                   Mem_CS <= 1'b1;
                   IR_Enable <= 1'b0;
                   RF_RegSel <= 4'b1111;
               end
               T <= 3'b000;
            end
            
            endcase
        
        end
        else if(T == 3) begin
            case(aluSystem.IROut[15:12])
            0001: begin
                MuxASel <= 2'b01;
                ARF_RegSel <= 3'b111;
                if (aluSystem.IROut[9:8] == 2'b00) begin
                    RF_RegSel <= 4'b0111;
                end else if (aluSystem.IROut[9:8] == 2'b01) begin
                    RF_RegSel <= 4'b1011;
                end else if (aluSystem.IROut[9:8] == 2'b10) begin
                    RF_RegSel <= 4'b1101;
                end else if (aluSystem.IROut[9:8] == 2'b11) begin
                    RF_RegSel <= 4'b1110;
                end
                RF_FunSel <= 2'b10;
                Mem_WR <= 1'b0
                Mem_CS <= 1'b0;
                IR_Enable <= 1'b0;
                T <= 3'b000;  
            end
            0010: begin
                RF_OutBSel <= aluSystem.IRout[9:8];
                ALU_FunSel <= 4'b0001;
                Mem_WR <= 1'b1;
                Mem_CS <= 1'b0;
                IR_Enable <= 1'b0;
                ARF_RegSel <= 3'b111;
                RF_RegSel <= 4'b1111;
                T <= 3'b000;
            end
            0100: begin
                ALU_FunSel <= 4'b0111;
                Mem_CS <= 1'b1;
                IR_Enable <= 1'b0;
                case(aluSystem.IROut[3:0])
                0000, 0001: begin
                    ARF_OutCSel <= 2'b00;
                    RF_RegSel <= 4'b1111;
                    MuxCSel <= 1'b0;
                end
                0010: begin
                    ARF_OutCSel <= 2'b10;
                    RF_RegSel <= 4'b1111;
                    MuxCSel <= 1'b0;
                end
                0011: begin
                    ARF_OutCSel <= 2'b11;
                    RF_RegSel <= 4'b1111;
                    MuxCSel <= 1'b0;
                end
                0100: begin
                    MuxCSel <= 1'b1;
                    RF_OutASel <= 2'b00;
                    RF_RegSel <= 4'b1111;
                end
                0101: begin
                    MuxCSel <= 1'b1;
                    RF_OutASel <= 2'b01;
                    RF_RegSel <= 4'b1111;
                end
                0110: begin
                    MuxCSel <= 1'b1;
                    RF_OutASel <= 2'b10;
                    RF_RegSel <= 4'b1111;
                end
                0111: begin
                    MuxCSel <= 1'b1;
                    RF_OutASel <= 2'b11;
                    RF_RegSel <= 4'b1111;
                end
                endcase
                case(aluSystem.IROut[11:8])
                0000, 0001: begin
                    MuxBSel <= 2'b11;
                    ARF_FunSel <= 2'b10;
                    ARF_RegSel <= 3'b011;
                    RF_RegSel <= 4'b1111;
                end
                0010: begin
                    MuxBSel <= 2'b11;
                    ARF_FunSel <= 2'b10;
                    ARF_RegSel <= 3'b101;
                    RF_RegSel <= 4'b1111;
                end
                0011: begin
                    MuxBSel <= 2'b11;
                    ARF_FunSel <= 2'b10;
                    ARF_RegSel <= 3'b110;
                    RF_RegSel <= 4'b1111;
                end
                0100: begin
                    MuxASel <= 2'b11;
                    RF_FunSel <= 2'b10;
                    RF_RegSel <= 4'b0111;
                    ARF_RegSel <= 3'b111;
                end
                0101: begin
                    MuxASel <= 2'b11;
                    RF_FunSel <= 2'b10;
                    RF_RegSel <= 4'b1011;
                    ARF_RegSel <= 3'b111;
                end
                0110: begin
                    MuxASel <= 2'b11;
                    RF_FunSel <= 2'b10;
                    RF_RegSel <= 4'b1101;
                    ARF_RegSel <= 3'b111;
                end
                0111: begin
                    MuxASel <= 2'b11;
                    RF_FunSel <= 2'b10;
                    RF_RegSel <= 4'b1110;
                    ARF_RegSel <= 3'b111;
                end
                endcase
                T <= 3'b000;
            end
            0101: begin
                ALU_FunSel <= 4'b1000;
                Mem_CS <= 1'b1;
                IR_Enable <= 1'b0;
                case(aluSystem.IROut[3:0])
                0000, 0001: begin
                    ARF_OutCSel <= 2'b00;
                    RF_RegSel <= 4'b1111;
                    MuxCSel <= 1'b0;
                end
                0010: begin
                    ARF_OutCSel <= 2'b10;
                    RF_RegSel <= 4'b1111;
                    MuxCSel <= 1'b0;
                end
                0011: begin
                    ARF_OutCSel <= 2'b11;
                    RF_RegSel <= 4'b1111;
                    MuxCSel <= 1'b0;
                end
                0100: begin
                    MuxCSel <= 1'b1;
                    RF_OutASel <= 2'b00;
                    RF_RegSel <= 4'b1111;
                end
                0101: begin
                    MuxCSel <= 1'b1;
                    RF_OutASel <= 2'b01;
                    RF_RegSel <= 4'b1111;
                end
                0110: begin
                    MuxCSel <= 1'b1;
                    RF_OutASel <= 2'b10;
                    RF_RegSel <= 4'b1111;
                end
                0111: begin
                    MuxCSel <= 1'b1;
                    RF_OutASel <= 2'b11;
                    RF_RegSel <= 4'b1111;
                end
                endcase
                case(aluSystem.IROut[11:8])
                0000, 0001: begin
                    MuxBSel <= 2'b11;
                    ARF_FunSel <= 2'b10;
                    ARF_RegSel <= 3'b011;
                    RF_RegSel <= 4'b1111;
                end
                0010: begin
                    MuxBSel <= 2'b11;
                    ARF_FunSel <= 2'b10;
                    ARF_RegSel <= 3'b101;
                    RF_RegSel <= 4'b1111;
                end
                0011: begin
                    MuxBSel <= 2'b11;
                    ARF_FunSel <= 2'b10;
                    ARF_RegSel <= 3'b110;
                    RF_RegSel <= 4'b1111;
                end
                0100: begin
                    MuxASel <= 2'b11;
                    RF_FunSel <= 2'b10;
                    RF_RegSel <= 4'b0111;
                    ARF_RegSel <= 3'b111;
                end
                0101: begin
                    MuxASel <= 2'b11;
                    RF_FunSel <= 2'b10;
                    RF_RegSel <= 4'b1011;
                    ARF_RegSel <= 3'b111;
                end
                0110: begin
                    MuxASel <= 2'b11;
                    RF_FunSel <= 2'b10;
                    RF_RegSel <= 4'b1101;
                    ARF_RegSel <= 3'b111;
                end
                0111: begin
                    MuxASel <= 2'b11;
                    RF_FunSel <= 2'b10;
                    RF_RegSel <= 4'b1110;
                    ARF_RegSel <= 3'b111;
                end
                endcase
                T <= 3'b000;
            end
            0111:begin
                ALU_FunSel <= 4'b0100;
                Mem_CS <= 1'b1;
                IR_Enable <= 1'b0;
                case(ALUSystem.IROut[3:0])
                    /*0000, 0001: begin
                        ARF_OutCSel <= 2'b00;
                        RF_RegSel <= 4'b1111;
                        MuxCSel <= 1'b0;
                    end
                    0010: begin
                        ARF_OutCSel <= 2'b10;
                        RF_RegSel <= 4'b1111;
                        MuxCSel <= 1'b0;
                    end
                    0011: begin
                        ARF_OutCSel <= 2'b11;
                        RF_RegSel <= 4'b1111;
                        MuxCSel <= 1'b0;
                    end*/
                    0100: begin
                        MuxCSel <= 1'b1;
                        RF_OutASel <= 2'b00;
                        RF_RegSel <= 4'b1111;
                    end
                    0101: begin
                        MuxCSel <= 1'b1;
                        RF_OutASel <= 2'b01;
                        RF_RegSel <= 4'b1111;
                    end
                    0110: begin
                        MuxCSel <= 1'b1;
                        RF_OutASel <= 2'b10;
                        RF_RegSel <= 4'b1111;
                    end
                    0111: begin
                        MuxCSel <= 1'b1;
                        RF_OutASel <= 2'b11;
                        RF_RegSel <= 4'b1111;
                    end                                                                                                            
                endcase
                case(aluSystem.IROut[11:8])
                    0000, 0001: begin
                        MuxBSel <= 2'b11;
                        ARF_FunSel <= 2'b10;
                        ARF_RegSel <= 3'b011;
                        RF_RegSel <= 4'b1111;
                    end
                    0010: begin
                        MuxBSel <= 2'b11;
                        ARF_FunSel <= 2'b10;
                        ARF_RegSel <= 3'b101;
                        RF_RegSel <= 4'b1111;
                    end
                    0011: begin
                        MuxBSel <= 2'b11;
                        ARF_FunSel <= 2'b10;
                        ARF_RegSel <= 3'b110;
                        RF_RegSel <= 4'b1111;
                    end
                    0100: begin
                        MuxASel <= 2'b11;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b0111;
                        ARF_RegSel <= 3'b111;
                    end
                    0101: begin
                        MuxASel <= 2'b11;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1011;
                        ARF_RegSel <= 3'b111;
                    end
                    0110: begin
                        MuxASel <= 2'b11;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1101;
                        ARF_RegSel <= 3'b111;
                    end
                    0111: begin
                        MuxASel <= 2'b11;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1110;
                        ARF_RegSel <= 3'b111;
                    end
                endcase
                T <= 3'b000;                
            end
            1000:begin
                ALU_FunSel <= 4'b0110;
                Mem_CS <= 1'b1;
                IR_Enable <= 1'b0;
                case(aluSystem.IROut[3:0])
                    /*0000, 0001: begin
                        ARF_OutCSel <= 2'b00;
                        RF_RegSel <= 4'b1111;
                        MuxCSel <= 1'b0;
                    end
                    0010: begin
                        ARF_OutCSel <= 2'b10;
                        RF_RegSel <= 4'b1111;
                        MuxCSel <= 1'b0;
                    end
                    0011: begin
                        ARF_OutCSel <= 2'b11;
                        RF_RegSel <= 4'b1111;
                        MuxCSel <= 1'b0;
                    end*/
                    0100: begin
                        MuxCSel <= 1'b1;
                        RF_OutASel <= 2'b00;
                        RF_RegSel <= 4'b1111;
                    end
                    0101: begin
                        MuxCSel <= 1'b1;
                        RF_OutASel <= 2'b01;
                        RF_RegSel <= 4'b1111;
                    end
                    0110: begin
                        MuxCSel <= 1'b1;
                        RF_OutASel <= 2'b10;
                        RF_RegSel <= 4'b1111;
                    end
                    0111: begin
                        MuxCSel <= 1'b1;
                        RF_OutASel <= 2'b11;
                        RF_RegSel <= 4'b1111;
                    end
                endcase
                case(aluSystem.IROut[11:8])
                    0000, 0001: begin
                        MuxBSel <= 2'b11;
                        ARF_FunSel <= 2'b10;
                        ARF_RegSel <= 3'b011;
                        RF_RegSel <= 4'b1111;
                    end
                    0010: begin
                        MuxBSel <= 2'b11;
                        ARF_FunSel <= 2'b10;
                        ARF_RegSel <= 3'b101;
                        RF_RegSel <= 4'b1111;
                    end
                    0011: begin
                        MuxBSel <= 2'b11;
                        ARF_FunSel <= 2'b10;
                        ARF_RegSel <= 3'b110;
                        RF_RegSel <= 4'b1111;
                    end
                    0100: begin
                        MuxASel <= 2'b11;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b0111;
                        ARF_RegSel <= 3'b111;
                    end
                    0101: begin
                        MuxASel <= 2'b11;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1011;
                        ARF_RegSel <= 3'b111;
                    end
                    0110: begin
                        MuxASel <= 2'b11;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1101;
                        ARF_RegSel <= 3'b111;
                    end
                    0111: begin
                        MuxASel <= 2'b11;
                        RF_FunSel <= 2'b10;
                        RF_RegSel <= 4'b1110;
                        ARF_RegSel <= 3'b111;
                    end
                endcase
                T <= 3'b000;                
            end
            1011:begin
                ARF_RegSel <= 3'b110;
                ARF_FunSel <= 2'b00;
                Mem_CS <= 1'b1;
                IR_Enable <= 1'b0;
                RF_RegSel <= 4'b1111;
                T <= 3'b000;   
            end
            endcase
        end
        
    end
    
endmodule