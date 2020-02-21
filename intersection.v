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
	wire pedestrian_active;

	wire up_request;
	wire up_blocked;
	wire up_active;

	wire down_request;
	wire down_blocked;
	wire down_active;

	wire turn_request;
	wire turn_blocked;
	wire turn_active;

	// ----- priority monitor -----

	reg [1:0] priority_pedestrian;
	reg [1:0] priority_up;
	reg [1:0] priority_down;
	reg [1:0] priority_turn;

	reg [1:0] priority_ceil;

	always @* begin
		priority_ceil = 0;
		if (pedestrian_green && priority_pedestrian != 0) priority_ceil = priority_pedestrian;
		if (        up_green && priority_up         != 0) priority_ceil = priority_up;
		if (      down_green && priority_down       != 0) priority_ceil = priority_down;
		if (      turn_green && priority_turn       != 0) priority_ceil = priority_turn;
	end

	always @(posedge clock) begin
		priority_pedestrian <= priority_pedestrian + (priority_pedestrian < priority_ceil);
		priority_up         <= priority_up         + (priority_up         < priority_ceil);
		priority_down       <= priority_down       + (priority_down       < priority_ceil);

		if (pedestrian_green) priority_pedestrian <= 0;
		if (        up_green) priority_up         <= 0;
		if (      down_green) priority_down       <= 0;
		if (      turn_green) priority_turn       <= 0;

		if (reset) begin
			priority_pedestrian <= 0;
			priority_up <= 1;
			priority_down <= 2;
			priority_turn <= 3;
		end
	end

	// ----- arbiter control -----

	assign pedestrian_request = pedestrian_button;
	assign pedestrian_blocked = up_active || down_active;

	assign up_request = 1;
	assign up_blocked = pedestrian_active;

	assign down_request = 1;
	assign down_blocked = pedestrian_active || turn_active;

	assign turn_request = turn_sensor;
	assign turn_blocked = down_active;

	// ----- lights -----

	trafficlight tl_pedestrian (
		.clock   (           clock  ),
		.reset   (           reset  ),
		.request (pedestrian_request),
		.blocked (pedestrian_blocked),
		.red     (pedestrian_red    ),
		.green   (pedestrian_green  ),
		.active  (pedestrian_active )
	);

	trafficlight tl_up (
		.clock   (           clock  ),
		.reset   (           reset  ),
		.request (        up_request),
		.blocked (        up_blocked),
		.red     (        up_red    ),
		.green   (        up_green  ),
		.active  (        up_active )
	);

	trafficlight tl_down (
		.clock   (           clock  ),
		.reset   (           reset  ),
		.request (      down_request),
		.blocked (      down_blocked),
		.red     (      down_red    ),
		.green   (      down_green  ),
		.active  (      down_active )
	);

	trafficlight tl_turn (
		.clock   (           clock  ),
		.reset   (           reset  ),
		.request (      turn_request),
		.blocked (      turn_blocked),
		.red     (      turn_red    ),
		.green   (      turn_green  ),
		.active  (      turn_active )
	);
endmodule
