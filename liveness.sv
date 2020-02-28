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

	default clocking @(posedge clock); endclocking
	default disable iff (reset);

	liveness_pedestrian: assert property (
		pedestrian_button |-> ##[1:50] pedestrian_green
	);

	liveness_turn: assert property (
		turn_sensor |-> ##[1:50] turn_green
	);

	liveness_up: assert property (
		##[1:50] up_green
	);
	liveness_down: assert property (
		##[1:50] down_green
	);
endmodule

bind intersection liveness checker_inst (.*);
