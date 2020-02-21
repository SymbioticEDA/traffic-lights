module safety (
	input clock,
	input reset,

	input pedestrian_button,
	input turn_sensor,

	input pedestrian_green,
	input up_green,
	input down_green,
	input turn_green
);
	reg reset_req = 1;

	always @(posedge clock) begin
		if (reset_req)
			assume (reset);
		reset_req <= 0;
	end

	default clocking @(posedge clock); endclocking
	default disable iff (reset);

    assert property (pedestrian_green |-> (!up_green && !down_green));
	assert property (turn_green |-> !down_green);

endmodule

bind intersection safety checker_inst (.*);
