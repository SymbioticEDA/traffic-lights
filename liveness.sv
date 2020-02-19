module liveness (
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

	assert property (
		@(posedge clock) disable iff (reset)
		pedestrian_button |-> ##[1:50] pedestrian_green
	);

	assert property (
		@(posedge clock) disable iff (reset)
		turn_sensor |-> ##[1:50] turn_green
	);

	assert property (
		@(posedge clock) disable iff (reset)
		##[1:50] up_green
	);
	assert property (
		@(posedge clock) disable iff (reset)
		##[1:50] down_green
	);
endmodule

bind intersection liveness checker_inst (.*);
