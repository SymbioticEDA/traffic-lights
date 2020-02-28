module intersection (
	input  clock,
	input  reset,

	input  pedestrian_button,
	output pedestrian_green,
	output pedestrian_red,

	output up_green,
	output up_red,

	output down_green,
	output down_red,

	input  turn_sensor,
	output turn_green,
	output turn_red
);
	wire pedestrian_request;
	wire pedestrian_blocked;
	wire pedestrian_waiting;

	wire up_request;
	wire up_blocked;
	wire up_waiting;

	wire down_request;
	wire down_blocked;
	wire down_waiting;

	wire turn_request;
	wire turn_blocked;
	wire turn_waiting;

	// ----- priority monitor -----

	// prioritize first when 0, second when 1
	reg pri_pedestrian_up;
	reg pri_pedestrian_down;
	reg pri_turn_down;

	always @(posedge clock) begin
		if (pedestrian_green) begin
			pri_pedestrian_up <= 1;
			pri_pedestrian_down <= 1;
		end
		if (up_green) begin
			pri_pedestrian_up <= 0;
		end
		if (down_green) begin
			pri_pedestrian_down <= 0;
			pri_turn_down <= 0;
		end
		if (turn_green) begin
			pri_turn_down <= 1;
		end
		if (reset) begin
			pri_pedestrian_up <= 0;
			pri_pedestrian_down <= 0;
			pri_turn_down <= 0;
		end
	end

	// ----- arbiter control -----

	assign pedestrian_request = pedestrian_button;
	assign pedestrian_blocked =
			(up_green || (up_waiting && pri_pedestrian_up)) ||
			(down_green || (down_waiting && pri_pedestrian_down));

	assign up_request = 1;
	assign up_blocked = pedestrian_green || (pedestrian_waiting && !pri_pedestrian_up);

	assign down_request = 1;
	assign down_blocked =
			(pedestrian_green || (pedestrian_waiting && !pri_pedestrian_down)) ||
			(turn_green || (turn_waiting && !pri_turn_down));

	assign turn_request = turn_sensor;
	assign turn_blocked = down_green || (down_waiting && pri_turn_down);

	// ----- lights -----

	trafficlight tl_pedestrian (
		.clock   (           clock  ),
		.reset   (           reset  ),
		.request (pedestrian_request),
		.blocked (pedestrian_blocked),
		.red     (pedestrian_red    ),
		.green   (pedestrian_green  ),
		.waiting (pedestrian_waiting)
	);

	trafficlight tl_up (
		.clock   (           clock  ),
		.reset   (           reset  ),
		.request (        up_request),
		.blocked (        up_blocked),
		.red     (        up_red    ),
		.green   (        up_green  ),
		.waiting (        up_waiting)
	);

	trafficlight tl_down (
		.clock   (           clock  ),
		.reset   (           reset  ),
		.request (      down_request),
		.blocked (      down_blocked),
		.red     (      down_red    ),
		.green   (      down_green  ),
		.waiting (      down_waiting)
	);

	trafficlight tl_turn (
		.clock   (           clock  ),
		.reset   (           reset  ),
		.request (      turn_request),
		.blocked (      turn_blocked),
		.red     (      turn_red    ),
		.green   (      turn_green  ),
		.waiting (      turn_waiting)
	);
endmodule
