/*
 *  Copyright (C) 2020  Claire Wolf <claire@symbioticeda.com>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

module miter (
	input  clock,
	input  reset,

	input  ref_pedestrian_button,
	input  ref_turn_sensor,
	input  uut_pedestrian_button,
	input  uut_turn_sensor,
);
	wire ref_pedestrian_green;
	wire uut_pedestrian_green;
	wire ref_up_green;
	wire uut_up_green;
	wire ref_down_green;
	wire uut_down_green;
	wire ref_turn_green;
	wire uut_turn_green;

    intersection ref (
        .clock              (clock),
        .reset              (reset),
	    .pedestrian_button  (ref_pedestrian_button),
	    .pedestrian_green   (ref_pedestrian_green),
	    .up_green           (ref_up_green),
	    .down_green         (ref_down_green),
	    .turn_sensor        (ref_turn_sensor),
	    .turn_green         (ref_turn_green),
        );

    intersection uut (
        .clock              (clock),
        .reset              (reset),
	    .pedestrian_button  (uut_pedestrian_button),
	    .pedestrian_green   (uut_pedestrian_green),
	    .up_green           (uut_up_green),
	    .down_green         (uut_down_green),
	    .turn_sensor        (uut_turn_sensor),
	    .turn_green         (uut_turn_green),
        );

	reg reset_req = 1;
	always @(posedge clock) begin
		if (reset_req)
			assume (reset);
		reset_req <= 0;
	end

	always @(posedge clock) begin
        assume (ref_pedestrian_button == uut_pedestrian_button);
        assume (ref_turn_sensor == uut_turn_sensor);
        if(!reset) begin
            assert (ref_up_green == uut_up_green);
            assert (ref_down_green == uut_down_green);
            assert (ref_pedestrian_green == uut_pedestrian_green);
        end
	end
endmodule
