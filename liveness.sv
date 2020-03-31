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
		pedestrian_button |-> ##[0:25] pedestrian_green
	);

endmodule

module intersection_invariants (
	input clock,
	input reset,

	input pedestrian_green,
	input up_green,
	input down_green,
	input turn_green
);
	default clocking @(posedge clock); endclocking
	default disable iff (reset);

	excl_pedestrian_up:   assert property (!(pedestrian_green &&   up_green));
	excl_pedestrian_down: assert property (!(pedestrian_green && down_green));
	excl_turn_down:       assert property (!(      turn_green && down_green));
endmodule

module trafficlight_invariants (
	input clock,
	input reset,

	input [7:0] state,
	input [31:0] counter
);
	default clocking @(posedge clock); endclocking
	default disable iff (reset);

	state_valid: assert property (
		(state == 0) || (state == 1) || (state == 2)
	);

	counter_valid: assert property (
		counter <= 5
	);
endmodule

bind intersection liveness checker_inst (.*);
bind intersection intersection_invariants invariants_inst (.*);
bind trafficlight trafficlight_invariants invariants_inst (.*);
