module simplecover (
	input clock,
	input reset,

	input pedestrian_green,
	input up_green,
	input down_green,
	input turn_green
);
	cover property (@(posedge clock) reset ##[+] pedestrian_green);
	cover property (@(posedge clock) reset ##[+] up_green);
	cover property (@(posedge clock) reset ##[+] down_green);
	cover property (@(posedge clock) reset ##[+] turn_green);
endmodule

bind intersection simplecover checker_inst (.*);
