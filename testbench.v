// Group 49
// Member Names: Yusuf Yaslan, Ali Esad Uğur, Hasan Fatih Durkaya
// IDs: 150190098, 150200050, 150200074

`timescale 1ns / 1ps
`include "modules.v"

module part1();
    reg [7:0] I;
    reg E;
    reg CLK;
    reg [1:0] FunSel;
    wire [7:0] Q;
    
    register8bit REG(I, E, CLK, FunSel, Q);
        
    initial begin
        CLK = 0; E = 0; I = 8'b10000000; FunSel=2'b00; #30;
        E = 1;
        FunSel = 2'b10; #50;
        FunSel = 2'b01; #50;
        FunSel = 2'b01; #50;
        FunSel = 2'b00; #50;
        FunSel = 2'b11; #50;
        E = 0; I = 8'b01000000; #50;
        E = 1;
        FunSel = 2'b10; #50;
        FunSel = 2'b01; #50;
        FunSel = 2'b00; #50;
        FunSel = 2'b11; #50;
        $finish;
    end
    
    always begin
       CLK <= ~CLK; #25;
    end
    
    always @(negedge CLK) begin
        $display("Register 8 Bit Input Values: I: %b, E: %b, FunSel: %b,", I, E, FunSel);
        $display("Register 8 Bit Output Values: Q: %b", Q);
        $display("");  
    end
    
endmodule

module part1_1();
    reg [15:0] I;
    reg E;
    reg CLK;
    reg [1:0] FunSel;
    wire [15:0] Q;
    
    register16bit REG(I, E, CLK, FunSel, Q);
        
    initial begin
        CLK = 0; E = 0; I = 16'b10000000; FunSel=2'b00; #30;
        E = 1;
        FunSel = 2'b10; #50;
        FunSel = 2'b01; #50;
        FunSel = 2'b01; #50;
        FunSel = 2'b00; #50;
        FunSel = 2'b11; #50;
        E = 0; I = 16'b01000000; #50;
        E = 1;
        FunSel = 2'b10; #50;
        FunSel = 2'b01; #50;
        FunSel = 2'b00; #50;
        FunSel = 2'b11; #50;
        $finish;
    end
    
    always begin
       CLK <= ~CLK; #25;
    end
    
    always @(negedge CLK) begin
        $display("Register 16 Bit Input Values: I: %b, E: %b, FunSel: %b,", I, E, FunSel);
        $display("Register 16 Bit Output Values: Q: %b", Q);
        $display("");  
    end
    
endmodule

module part2_a();
    reg [7:0] I;
    reg [1:0] outASel;
    reg [1:0] outBSel;
    reg [1:0] FunSel;
    reg [3:0] RegSel;
    reg CLK;
    
    wire [7:0] outA;
    wire [7:0] outB;
    
    register_file REG_FILE(I, outASel, outBSel, FunSel, RegSel, CLK, outA, outB);

    initial begin
        CLK = 0;
        I = 8'b00000000; outASel = 2'b00; outBSel = 2'b01; FunSel = 2'b10; RegSel = 4'b0000; #30;
        RegSel = 4'b0011; FunSel = 2'b01;#300;
        RegSel = 4'b1100; outASel = 2'b10; outBSel = 2'b11; #340;
        $finish;
    end

    always begin
       #25; CLK <= ~CLK; 
    end
    
    always @(negedge CLK) begin
        $display("Register File Input Values: I: %b, OutASel: %b, OutBSel: %b, FunSel: %b, RegSel: %b,", I, outASel, outBSel, FunSel, RegSel);
        $display("Register File Output Values: OutA: %b, OutB: %b", outA, outB);
        $display("");  
    end

endmodule

module part2_b();
    reg [7:0] I;
    reg [1:0] outCSel;
    reg [1:0] outDSel;
    reg [1:0] FunSel;
    reg [2:0] RegSel;
    reg CLK;
    
    wire [7:0] outC;
    wire [7:0] outD;
    
    address_register_file ADD_REG_FILE(I, outCSel, outDSel, FunSel, RegSel, CLK, outC, outD);

    initial begin
        CLK = 0;
        I = 8'b00000000; outCSel = 2'b00; outDSel = 2'b10; FunSel = 2'b10; RegSel = 3'b000; #30;
        RegSel = 3'b001; FunSel = 2'b01; I = 8'b11111111; #300;
        RegSel = 3'b100; outCSel = 2'b10; outDSel = 2'b11; #340;
        $finish;
    end

    always begin
       #25; CLK <= ~CLK; 
    end
    
    always @(negedge CLK) begin
        $display("Address Register File Input Values: I: %b, OutCSel: %b, OutDSel: %b, FunSel: %b, RegSel: %b,", I, outCSel, outDSel, FunSel, RegSel);
        $display("Address Register File Output Values: OutC: %b, OutD: %b", outC, outD);
        $display("");  
    end

endmodule

module part2_c();
    reg [7:0] I;
    reg E;
    reg LH;
    reg CLK;
    reg [1:0] FunSel;
    wire [15:0] Q;
    
    IR_register IR(I, E, LH, CLK, FunSel, Q);
        
    initial begin
        CLK = 0; E = 0; I = 8'b11111110; FunSel=2'b00; LH = 0; #30;
        E = 1;
        FunSel = 2'b10; #50;
        LH = 1;
        FunSel = 2'b10; #50;
        FunSel = 2'b01; #50;
        FunSel = 2'b01; #50;
        FunSel = 2'b00; #50;
        FunSel = 2'b11; #50;
        E = 0; I = 8'b01010101; #50;
        E = 1;
        FunSel = 2'b10; #50;
        FunSel = 2'b01; #50;
        FunSel = 2'b00; #50;
        FunSel = 2'b11; #50;
        $finish;
    end
    
    always begin
       CLK <= ~CLK; #25;
    end
    
    always @(negedge CLK) begin
        $display("IR Register Input Values: I: %b, E: %b, L_H: %b, FunSel: %b", I, E, LH, FunSel);
        $display("IR Register Output Values: Q: %b", Q);
        $display("");  
    end
    
endmodule

module ALU_test();
    reg [3:0] FunSel;
    reg [7:0] A;
    reg [7:0] B;
    
    wire [7:0] OutALU;
    wire [3:0] OutFlag;
    
    reg [4:0] func = 5'd0;
    
    ALU uut(A, B, FunSel, OutALU, OutFlag);
    
    initial begin
        # 10 FunSel = 4'b0000; A = 8'd0; B = 8'd0;
        # 10 A = 8'b0111_1111; B = 8'd1;                      
        for(func = 0; func <= 15; func = func + 1) begin
            FunSel = func; #20;
            $display("ALU Input Values: A: %b, B: %b, FunSel: %b", A, B, FunSel);
            $display("ALU Output Values: OutALU: %b, OutFlag: %b", OutALU, OutFlag);
            $display("");  
        end        
        $finish;
    end
    
    always begin
       CLK <= ~CLK; #25;
    end

    
endmodule


module Project1Test();
    //Input Registers of ALUSystem
    reg[1:0] RF_OutASel; 
    reg[1:0] RF_OutBSel; 
    reg[1:0] RF_FunSel;
    reg[3:0] RF_RegSel;
    reg[3:0] ALU_FunSel;
    reg[1:0] ARF_OutCSel; 
    reg[1:0] ARF_OutDSel; 
    reg[1:0] ARF_FunSel;
    reg[2:0] ARF_RegSel;
    reg      IR_LH;
    reg      IR_Enable;
    reg[1:0]      IR_Funsel;
    reg      Mem_WR;
    reg      Mem_CS;
    reg[1:0] MuxASel;
    reg[1:0] MuxBSel;
    reg MuxCSel;
    reg      Clock;
    
    //Test Bench Connection of ALU System
    ALUSystem _ALUSystem(
    .RF_OutASel(RF_OutASel), 
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
    .Clock(Clock)
    );
    
    //Test Vector Variables
    reg [31:0] VectorNum, Errors, TotalLine; 
    reg [34:0] TestVectors[10000:0];
    reg Reset, Operation;
    
    //Clock Signal Generation
    always 
    begin
        Clock = 1; #5; Clock = 0; #5; // 10ns period
    end
    
    //Read Test Bench Values
    initial begin
        $readmemb("TestBench.mem", TestVectors); // Read vectors
        VectorNum = 0; Errors = 0; TotalLine=0; Reset=0;// Initialize
    end
    
    // Apply test vectors on rising edge of clock
    always @(posedge Clock)
    begin
        #1; 
        {Operation, RF_OutASel, RF_OutBSel, RF_FunSel, 
        RF_RegSel, ALU_FunSel, ARF_OutCSel, ARF_OutDSel, 
        ARF_FunSel, ARF_RegSel, IR_LH, IR_Enable, IR_Funsel, 
        Mem_WR, Mem_CS, MuxASel, MuxBSel, MuxCSel} = TestVectors[VectorNum];
    end
    
    // Check results on falling edge of clk
    always @(negedge Clock)
        if (~Reset) // skip during reset
        begin
            $display("Input Values:");
            $display("Operation: %d", Operation);
            $display("Register File: OutASel: %d, OutBSel: %d, FunSel: %d, Regsel: %d", RF_OutASel, RF_OutBSel, RF_FunSel, RF_RegSel);            
            $display("ALU FunSel: %d", ALU_FunSel);
            $display("Addres Register File: OutCSel: %d, OutDSel: %d, FunSel: %d, Regsel: %d", ARF_OutCSel, ARF_OutDSel, ARF_FunSel, ARF_RegSel);            
            $display("Instruction Register: LH: %d, Enable: %d, FunSel: %d", IR_LH, IR_Enable, IR_Funsel);            
            $display("Memory: WR: %d, CS: %d", Mem_WR, Mem_CS);
            $display("MuxASel: %d, MuxBSel: %d, MuxCSel: %d", MuxASel, MuxBSel, MuxCSel);
            
            $display("");
            $display("Ouput Values:");
            $display("Register File: AOut: %b, BOut: %b", _ALUSystem.AOut, _ALUSystem.BOut);            
            $display("ALUOut: %b, ALUOutFlag: %b, ALUOutFlags: Z:%b, C:%b, N:%b, O:%b,", _ALUSystem.ALUOut, _ALUSystem.ALUOutFlag, _ALUSystem.ALUOutFlag[3],_ALUSystem.ALUOutFlag[2],_ALUSystem.ALUOutFlag[1],_ALUSystem.ALUOutFlag[0]);
            $display("Address Register File: COut: %d, DOut (Address): %d", _ALUSystem.ARF_COut, _ALUSystem.Address);            
            $display("Memory Out: %b", _ALUSystem.MemoryOut);            
            $display("Instruction Register: IROut: %d", _ALUSystem.IROut);            
            $display("MuxAOut: %d, MuxBOut: %d, MuxCOut: %d", _ALUSystem.MuxAOut, _ALUSystem.MuxBOut, _ALUSystem.MuxCOut);
            
            // increment array index and read next testvector
            VectorNum = VectorNum + 1;
            if (TestVectors[VectorNum] === 35'bx)
            begin
                $display("%d tests completed.",
                VectorNum);
                $finish; // End simulation
            end
        end
endmodule

module memory_tb();
    reg [7:0] address;
    reg [7:0] data;
    reg wr;
    reg cs;
    reg clock;
    wire [7:0] o;

    Memory mem(.address(address), .data(data), .wr(wr), .cs(cs), .clock(clock), .o(o));

    initial begin
        $display("Memory Input Values: address: %b, data: %b, wr: %b, cs: %b,", address, data, wr, cs);
        $display("Memory Output Values: MemoryOut: %b", o);
        $display("");  
        
        address = 8'd0; data = 8'h11; wr = 1; cs = 0; clock = 0; #25;
        $display("Memory Input Values: address: %b, data: %b, wr: %b, cs: %b,", address, data, wr, cs);
        $display("Memory Output Values: MemoryOut: %b", o);
        $display("");  
        
        address = 8'd16; data = 8'h11; wr = 1; cs = 0; clock = 1; #5;
        $display("Memory Input Values: address: %b, data: %b, wr: %b, cs: %b,", address, data, wr, cs);
        $display("Memory Output Values: MemoryOut: %b", o);
        $display("");  
        
        clock = 0; #25;
        address = 8'd16; wr = 0; cs = 0; clock = 0; #25;
        $display("Memory Input Values: address: %b, data: %b, wr: %b, cs: %b,", address, data, wr, cs);
        $display("Memory Output Values: MemoryOut: %b", o);
        $display("");  
    end
endmodule