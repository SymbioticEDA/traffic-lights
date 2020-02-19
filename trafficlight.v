module trafficlight (
	input clock,
	input reset,
	input request,
	input blocked,
	output red,
	output green,
	output active
);
	reg [7:0] state;
	reg [31:0] counter;

`ifdef FORMAL
	localparam [31:0] GREEN_PERIOD = 5;
`else
	localparam [31:0] GREEN_PERIOD = 10000;
`endif

	localparam [7:0] STATE_IDLE = 0;
	localparam [7:0] STATE_WAIT = 1;
	localparam [7:0] STATE_GREEN = 2;

	always @(posedge clock) begin
		if (reset) begin
			state <= STATE_IDLE;
			counter <= GREEN_PERIOD;
		end else
		case (state)
			STATE_IDLE: begin
				if (request)
					state <= STATE_WAIT;
			end
			STATE_WAIT: begin
				if (!blocked)
					state <= STATE_GREEN;
			end
			STATE_GREEN: begin
				counter <= counter - 1;
				if (counter == 0) begin
					counter <= GREEN_PERIOD;
					state <= STATE_IDLE;
				end
			end
		endcase
	end

	assign active = state != STATE_IDLE;
	assign green = state == STATE_GREEN;
	assign red = !green;
endmodule
