module simplecover (
	input clock,
	input reset,

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

	cover property (pedestrian_green);
	cover property (up_green);
	cover property (down_green);
	cover property (turn_green);

	property signal_pair(first, second);
		(first && !second) ##[+] (!first && second);
	endproperty

	pair_pedestrian_up:   cover property (signal_pair(pedestrian_green, up_green));
	pair_pedestrian_down: cover property (signal_pair(pedestrian_green, down_green));
	pair_pedestrian_turn: cover property (signal_pair(pedestrian_green, turn_green));

	pair_up_pedestrian:   cover property (signal_pair(up_green, pedestrian_green));
	pair_up_down:         cover property (signal_pair(up_green, down_green));
	pair_up_turn:         cover property (signal_pair(up_green, turn_green));

	pair_down_pedestrian: cover property (signal_pair(down_green, pedestrian_green));
	pair_down_up:         cover property (signal_pair(down_green, up_green));
	pair_down_turn:       cover property (signal_pair(down_green, turn_green));

//	pair_turn_pedestrian: cover property (signal_pair(turn_green, pedestrian_green));   <-- BUG?
	pair_turn_up:         cover property (signal_pair(turn_green, up_green));
	pair_turn_down:       cover property (signal_pair(turn_green, down_green));
endmodule

bind intersection simplecover checker_inst (.*);
