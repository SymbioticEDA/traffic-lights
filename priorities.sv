module priorities (
	input clock,
	input reset,

	input [1:0] priority_pedestrian,
	input [1:0] priority_up,
	input [1:0] priority_down,
	input [1:0] priority_turn
);
	reg reset_req = 1;

	always @(posedge clock) begin
		if (reset_req)
			assume (reset);
		reset_req <= 0;
	end

	always @* begin
		if (!reset) begin
			assert (priority_pedestrian == 0 || priority_up == 0 || priority_down == 0 || priority_turn == 0);
			assert (priority_pedestrian == 1 || priority_up == 1 || priority_down == 1 || priority_turn == 1);
			assert (priority_pedestrian == 2 || priority_up == 2 || priority_down == 2 || priority_turn == 2);
			assert (priority_pedestrian == 3 || priority_up == 3 || priority_down == 3 || priority_turn == 3);
		end
	end
endmodule

bind intersection priorities checker_inst (.*);
