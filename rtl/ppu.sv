// Copyright (c) 2012-2013 Ludvig Strigeus
// This program is GPL Licensed. See COPYING for the full license.

// altera message_off 10935
// altera message_off 10027

// Disable this for more dainty FPGAs
`define EXTRA_SPRITES

// Generates the current scanline / cycle counters
module ClockGen(
	input  logic       clk,
	input  logic       ce,
	input  logic       ce2,
	input  logic       reset,
	input  logic [1:0] sys_type,
	input  logic       rendering_enabled,
	output logic       held_reset,
	output logic [8:0] scanline,
	output logic [8:0] cycle,
	output logic       end_of_line,
	output logic       at_last_cycle_group,
	output logic       exiting_vblank,
	output logic       entering_vblank,
	output logic       short_frame,
	output logic       clr_vbl_ovf_sp0,
	output logic       is_pre_render,
	output logic       is_visible,
	output logic       is_rendering,
	output logic       pclk0,        // Phase clock 0
	output logic       pclk1         // Phase clock 1
);

// State
logic even_frame_toggle = 0; // 1 indicates even frame.

// Ephmeral state
logic [1:0] clk_delay;

// Nonvolatile State
logic [8:0] vblank_start_sl;
logic [8:0] vblank_end_sl;
logic skip_en;

// Continuous Intermediates
logic skip_dot;
logic clr_vbl_ovf_sp0_1;
logic entering_vblank_1;

assign pclk0 = ce;
assign pclk1 = ce2;

// The pre render flag is set while we're on scanline -1.
assign is_rendering = rendering_enabled & (is_visible | is_pre_render);
assign at_last_cycle_group = (cycle[8:3] == 42);

// For NTSC only, the *last* cycle of odd frames is skipped. This signal is for de-jitter.
assign short_frame = skip_dot & pclk0;

// All vblank clocked registers should have changed and be readable by cycle 1 of the vblank scanlines
assign entering_vblank = (cycle == 0) && scanline == vblank_start_sl;
assign exiting_vblank = clr_vbl_ovf_sp0;

assign skip_dot = clr_vbl_ovf_sp0 && ~even_frame_toggle && skip_en && (cycle == 339 && is_rendering);

always @(posedge clk) if (reset) begin
	cycle <= 9'd0;
	scanline <= 9'd0;
	even_frame_toggle <= 0;
	held_reset <= 1;
	is_visible <= 0;
	end_of_line <= 0;
	clr_vbl_ovf_sp0 <= 0;
	is_pre_render <= 0;

	case (sys_type)
		2'b00,2'b11: begin // NTSC/Vs.
			vblank_start_sl <= 9'd241;
			vblank_end_sl   <= 9'd260;
			skip_en         <= 1'b1;
		end

		2'b01: begin       // PAL
			vblank_start_sl <= 9'd241;
			vblank_end_sl   <= 9'd310;
			skip_en         <= 1'b0;
		end

		2'b10: begin       // Dendy
			vblank_start_sl <= 9'd291;
			vblank_end_sl   <= 9'd310;
			skip_en         <= 1'b0;
		end
	endcase
end else begin
	if (pclk1) begin // The determinaton to advance to the next line is made at pclk1
		end_of_line <= skip_dot || cycle == 340;
		clr_vbl_ovf_sp0 <= is_pre_render;
	end

	if (pclk0) begin
		cycle <= cycle + 9'd1;
		if (clr_vbl_ovf_sp0) begin
			held_reset <= 0;
			is_visible <= 1;
		end

		if (end_of_line) begin
			cycle <= 9'd0;

			if (scanline == 239)
				is_visible <= 0;
			// Once the scanline counter reaches end of 260, it gets reset to -1.
			if (scanline == vblank_end_sl) begin
				scanline <= 9'd511;
				is_pre_render <= 1;
			end else begin
				scanline <= scanline + 1'd1;
				is_pre_render <= 0;
			end

			if (scanline == 255)
				even_frame_toggle <= ~even_frame_toggle;
		end
	end
end

endmodule // ClockGen

module VramGen (
	input  logic        clk,
	input  logic        reset,
	input  logic        ce,
	input  logic        pclk1,
	input  logic        read_ce,
	input  logic        write_ce,
	input  logic        is_rendering,
	input  logic        rendering_enabled,
	input  logic  [2:0] ain,           // input address from CPU
	input  logic  [7:0] din,           // data input
	input  logic        read,          // read
	input  logic        write,         // write
	input  logic        is_pre_render, // Is this the pre-render scanline
	input  logic  [8:0] cycle,
	input  logic        ppu_incr,
	input  logic        HVTog,
	output logic [14:0] vram_v,
	output logic  [2:0] fine_x_scroll  // Current fine_x_scroll value
);

// Temporary VRAM address register
logic [14:0] vram_t;

// SR To delay 2006 copy to vram_v
logic [3:0] delayed_2006_write;
logic pending_2006_trig;

// Other intermediates
logic [14:0] vram_t_mask;
logic trigger_2007;
logic trigger_2007_cur;
logic trigger_2007_latch;

logic write_2006, write_2006_1, write_2006_2;

// VRAM_v reference:
// [14 13 12] [11 10] [9 8 7 6 5] [4 3 2 1 0]
//  Fine Y     NT Sel  Coarse Y    Coarse X
// Fine X is its own seperate register.

// Performs the glitchy vram_scroll used by Burai Fighter and some others
// FIXME: Assumes 1 pclk0 tick per read/write. Should be delayed to falling edge of phi2?
assign trigger_2007 = ((read || write) && ain == 7);
// Mask used to simulate glitchy behavior caused by a 2006 delayed write landing on the same cycle
// as natural copy from t->v
assign vram_t_mask = write_2006 ? vram_t : 15'h7FFF;

logic read_n;
logic write_n;
logic old_read;
logic old_write;
logic [2:0] last_ain;

assign read_n = ~read & old_read;
assign write_n = ~write & old_write;

always @(posedge clk) if (reset) begin
	vram_t <= 0;
	fine_x_scroll <= 0;
end else begin
	old_read <= read;
	old_write <= write;
	last_ain <= ain;

	// Copies from T to V are delayed by 1 pclk1 and then 2 pclk0 cycles after the second 2006 write
	if (pclk1) begin
		pending_2006_trig <= 0;
		write_2006_1 <= pending_2006_trig;
	end

	if (ce) begin
		write_2006_2 <= write_2006_1;
		write_2006 <= write_2006_2;
	end

	if (pclk1) begin
		// Horizontal copy at cycle 257 and rendering OR if delayed 2006 write
		if (is_rendering && cycle == 256 || write_2006)
			{vram_v[10], vram_v[4:0]} <= {vram_t[10], vram_t[4:0]};

		// Vertical copy at Cycles 280 to 305 and rendering OR delayed 2006 write
		if (cycle >= 279 && cycle < 304 && is_pre_render && rendering_enabled || write_2006)
			{vram_v[14:11], vram_v[9:5]} <= {vram_t[14:11], vram_t[9:5]};

		// Increment course X scroll from (cycle 0-255 or 320-335) and cycle[2:0] == 7
		if (is_rendering && ((cycle[2:0] == 7 && (~cycle[8] || (cycle[8] && cycle[6]))) || trigger_2007)) begin
			vram_v[4:0] <= (vram_v[4:0] + 1'd1) & vram_t_mask[4:0];
			vram_v[10] <= (vram_v[10] ^ &vram_v[4:0]) & vram_t_mask[10];
		end

		// Vertical Increment at 256 and rendering
		if (is_rendering && (cycle == 255 || trigger_2007)) begin
			vram_v[14:12] <= (vram_v[14:12] + 1'd1) & vram_t_mask[14:12];
			vram_v[9:5] <= vram_v[9:5] & vram_t_mask[9:5];
			vram_v[11] <= vram_v[11] & vram_t_mask[11];
			if (vram_v[14:12] == 7) begin
				if (vram_v[9:5] == 29) begin
					vram_v[9:5] <= 0;
					vram_v[11] <= ~vram_v[11] & vram_t_mask[11];
				end else begin
					vram_v[9:5] <= (vram_v[9:5] + 1'd1) & vram_t_mask[9:5];
				end
			end
		end
	end

	if (write_ce && ain == 6 && HVTog)
		pending_2006_trig <= 1;

	if (write && ain == 0) begin
		vram_t[10] <= din[0];
		vram_t[11] <= din[1];
	end else if (write && ain == 5) begin
		if (!HVTog) begin
			vram_t[4:0] <= din[7:3];
			fine_x_scroll <= din[2:0];
		end else begin
			vram_t[9:5] <= din[7:3];
			vram_t[14:12] <= din[2:0];
		end
	end else if (write && ain == 6) begin
		if (!HVTog) begin
			vram_t[13:8] <= din[5:0];
			vram_t[14] <= 0;
		end else begin
			vram_t[7:0] <= din;
		end
	end else if (last_ain == 7 && (read_n || write_n) && ~is_rendering) begin
		// Increment address every time we accessed a reg
		vram_v <= vram_v + (ppu_incr ? 15'd32 : 15'd1);
	end
end

endmodule


// 8 of these exist, they are used to output sprites.
module Sprite(
	input clk,
	input ce,
	input enable,
	input [3:0] load,
	input [26:0] load_in,
	output [26:0] load_out,
	output [4:0] bits // Low 4 bits = pixel, high bit = prio
);

reg [1:0] upper_color; // Upper 2 bits of color
reg [7:0] x_coord;     // X coordinate where we want things
reg [7:0] pix1, pix2;  // Shift registers, output when x_coord == 0
reg aprio;             // Current prio
wire active = (x_coord == 0);

always @(posedge clk) if (ce) begin
	if (enable) begin
		if (!active) begin
			// Decrease until x_coord is zero.
			x_coord <= x_coord - 8'h01;
		end else begin
			pix1 <= pix1 >> 1;
			pix2 <= pix2 >> 1;
		end
	end
	if (load[3]) pix1 <= load_in[26:19];
	if (load[2]) pix2 <= load_in[18:11];
	if (load[1]) x_coord <= load_in[10:3];
	if (load[0]) {upper_color, aprio} <= load_in[2:0];
end
assign bits = {aprio, upper_color, active && pix2[0], active && pix1[0]};
assign load_out = {pix1, pix2, x_coord, upper_color, aprio};

endmodule  // SpriteGen

// This contains all sprites. Will return the pixel value of the highest prioritized sprite.
// When load is set, and clocked, load_in is loaded into sprite 15 and all others are shifted down.
// Sprite 0 has highest prio.
module SpriteSet(
	input clk,
	input ce,               // Input clock
	input enable,           // Enable pixel generation
	input [3:0] load,       // Which parts of the state to load/shift.
	input [3:0] load_ex,    // Which parts of the state to load/shift for extra sprites.
	input [26:0] load_in,   // State to load with
	input [26:0] load_in_ex,// Extra spirtes
	output [4:0] bits,      // Output bits
	output is_sprite0,       // Set to true if sprite #0 was output
	input extra_sprites
);

wire [26:0] load_out7, load_out6, load_out5, load_out4, load_out3, load_out2, load_out1, load_out0,
	load_out15, load_out14, load_out13, load_out12, load_out11, load_out10, load_out9, load_out8;
wire [4:0] bits7, bits6, bits5, bits4, bits3, bits2, bits1, bits0,
	bits15, bits14, bits13, bits12, bits11, bits10, bits9, bits8;

`ifdef EXTRA_SPRITES
// Extra sprites
Sprite sprite15(clk, ce, enable, load_ex, load_in_ex, load_out15, bits15);
Sprite sprite14(clk, ce, enable, load_ex, load_out15, load_out14, bits14);
Sprite sprite13(clk, ce, enable, load_ex, load_out14, load_out13, bits13);
Sprite sprite12(clk, ce, enable, load_ex, load_out13, load_out12, bits12);
Sprite sprite11(clk, ce, enable, load_ex, load_out12, load_out11, bits11);
Sprite sprite10(clk, ce, enable, load_ex, load_out11, load_out10, bits10);
Sprite sprite9( clk, ce, enable, load_ex, load_out10, load_out9,  bits9);
Sprite sprite8( clk, ce, enable, load_ex, load_out9,  load_out8,  bits8);
`endif

// Basic Sprites
Sprite sprite7( clk, ce, enable, load, load_in,    load_out7,  bits7);
Sprite sprite6( clk, ce, enable, load, load_out7,  load_out6,  bits6);
Sprite sprite5( clk, ce, enable, load, load_out6,  load_out5,  bits5);
Sprite sprite4( clk, ce, enable, load, load_out5,  load_out4,  bits4);
Sprite sprite3( clk, ce, enable, load, load_out4,  load_out3,  bits3);
Sprite sprite2( clk, ce, enable, load, load_out3,  load_out2,  bits2);
Sprite sprite1( clk, ce, enable, load, load_out2,  load_out1,  bits1);
Sprite sprite0( clk, ce, enable, load, load_out1,  load_out0,  bits0);

// Determine which sprite is visible on this pixel.
assign bits = bits_orig;
wire [4:0] bits_orig =
	bits0[1:0]  != 0 ? bits0 :
	bits1[1:0]  != 0 ? bits1 :
	bits2[1:0]  != 0 ? bits2 :
	bits3[1:0]  != 0 ? bits3 :
	bits4[1:0]  != 0 ? bits4 :
	bits5[1:0]  != 0 ? bits5 :
	bits6[1:0]  != 0 ? bits6 :
	bits7[1:0]  != 0 || ~extra_sprites ? bits7 :
`ifdef EXTRA_SPRITES
	bits_ex;

wire [4:0] bits_ex =
	bits8[1:0]  != 0 ? bits8 :
	bits9[1:0]  != 0 ? bits9 :
	bits10[1:0] != 0 ? bits10 :
	bits11[1:0] != 0 ? bits11 :
	bits12[1:0] != 0 ? bits12 :
	bits13[1:0] != 0 ? bits13 :
	bits14[1:0] != 0 ? bits14 :
	bits15;
`else
	bits7;
`endif

assign is_sprite0 = bits0[1:0] != 0;

endmodule  // SpriteSet

module OAMEval(
	input  logic        clk,
	input  logic        ce,
	input  logic        ce2,
	input  logic        reset,
	input  logic        clr_vbl_ovf_sp0,
	input  logic        rendering_enabled,    // Set to 1 if evaluations are enabled
	input  logic        obj_size,             // Set to 1 if objects are 16 pixels.
	input  logic  [8:0] scanline,             // Current scan line (compared against Y)
	input  logic  [8:0] cycle,                // Current cycle.
	input  logic        oam_addr_write,       // Load oam with specified value, when writing to NES $2003.
	input  logic        oam_data_write,       // Load oam_ptr with specified value, when writing to NES $2004.
	input  logic        oam_data_read,        // read
	input  logic  [7:0] oam_din,              // New value for oam or oam_ptr
	input  logic        is_pre_render,        // Is the pre-render scanline
	input  logic        is_visible,           // In the visible scanline range <240
	input  logic        end_of_line,          // Last pixel of the line
	input  logic        PAL,
	output logic        spr_overflow,         // Set to true if we had more than 8 objects on a scan line.
	output logic        sprite0,              // True if sprite#0 is included on the scan line currently being painted.
	output logic  [7:0] oam_bus,              // Current value on the OAM bus, returned to NES through $2004.
	output logic  [7:0] oam_read_bus,
	output logic [3:0][7:0] oam_bus_ex,           // Load out for extra sprites
	output logic        masked_sprites,       // If the game is trying to mask extra sprites
	output logic        sprite_load
);

// https://wiki.nesdev.com/w/index.php/PPU_sprite_evaluation

logic oam_wr;
logic [7:0] oamd;
logic [7:0] oamxd;
assign sprite_load = (oam_state == STATE_FETCH);
assign oam_bus = oam_data;

//assign oam_data = oam_db;

enum logic [2:0] {
	STATE_CLEAR   = 3'd1,
	STATE_EVAL    = 3'd2,
	STATE_FETCH   = 3'd3,
	STATE_REFRESH = 3'd4
} oam_state;

// reg [7:0] oam_temp[64];    // OAM Temporary buffer, normally 32 bytes, 64 for extra sprites
//reg [7:0] oam[256];        // OAM RAM, 256 bytes
reg [7:0] oam_addr;        // OAM Address Register 2003
reg [2:0] oam_temp_slot;   // Pointer to oam_temp;
reg [7:0] oam_data;        // OAM Data Register 2004
reg oam_temp_wren;         // Write enable for OAM temp, disabled if full
logic [7:0] oam_addr_ex;     // OAM pointer for use with extra sprites
logic [3:0] oam_temp_slot_ex;

// Extra Registers
`ifdef EXTRA_SPRITES
reg [1:0] m_ex;
reg [7:0] oam_ex_data;
reg [2:0] spr_counter;     // Count sprites
`endif

				// int32_t pos = ppu->dot - 258;
				// int32_t n = pos / 8;
				// int32_t m = (pos % 8 > 3) ? 3 : pos % 8;

				// v = ppu->open_bus =
				// 	(pos >= 0 && n < 8) ? ppu->soam[n][m] :
				// 	(ppu->dot < 65 || (ppu->soam_n == 8 && (ppu->dot & 0x01) == 0)) ? ppu->soam[0][0] :
				// 	ppu->oam[ppu->OAMADDR];

wire rendering = (is_visible | is_pre_render) & (rendering_enabled | (PAL && scanline > 260));
wire evaluating = rendering & ~is_pre_render;

reg [6:0] feed_cnt;

reg sprite0_curr;
logic [4:0] repeat_count;

logic [7:0] oam_addr_adj;
logic ram_corruption_phase;
logic ram_corruption_write;
logic [7:0] oam_data_adj;
logic [7:0] oamtd, oamxtd;
logic [7:0] ram_corruption_data;
logic [8:0] last_cycle;

logic [7:0] sprite_data_ex[4] = '{8'hFF, 8'hFF, 8'hFF, 8'hFF};
logic [7:0] sprite_compare[4] = '{8'hFF, 8'hFF, 8'hFF, 8'hFF};

assign last_cycle = cycle;

// If OAMADDR is not less than eight when rendering starts, the eight bytes starting at OAMADDR &
// 0xF8 are copied to the first eight bytes of OAM

assign ram_corruption_phase = ~|cycle[8:4] && is_pre_render && rendering && oam_addr > 8 && ~PAL;

assign oam_addr_adj = ram_corruption_phase ? (~write_cycle ? {oam_addr[7:3], last_cycle[3:1]} : {5'd0, last_cycle[3:1]}) : oam_addr;
assign ram_corruption_write = ram_corruption_phase && write_cycle;
assign oam_data_adj = ram_corruption_phase ? ram_corruption_data : (oam_addr[1:0] == 2'b10) ? {oam_din[7:5], 3'b000, oam_din[1:0]} : oam_din;

dpram #(.widthad_a(8), .width_a(8)) OAM_ram //256 * 8 bits
(
	.clock_a   (clk),
	.address_a (oam_addr_adj),
	.data_a    (oam_data_adj), // byte 3 has no bits 2-4
	.wren_a    (oam_data_write | ram_corruption_write),
	.q_a       (oamd),

	.clock_b   (clk),
	.address_b (oam_addr_ex),
	.wren_b    (0),
	.q_b       (oamxd)
);

logic [6:0] oam_temp_full_addr;
logic [6:0] oam_temp_ex_full_addr;
logic [7:0] oam_ex_db;

logic oam_temp_wren_adj, oam_temp_ex_wren;
reg n_ovr, ex_ovr;
logic write_cycle;
assign write_cycle = cycle[0];



always_comb begin
	if (cycle < 64) //~|cycle[8:6]
		oam_state = STATE_CLEAR;   // 64 cycles
	else if (cycle < 256)  // ~cycle[8]
		oam_state = STATE_EVAL;    // 192 cycles
	else if (cycle < 320)  // cycle[8] & ~cycle[6]
		oam_state = STATE_FETCH;   // 64 cycles
	else
		oam_state = STATE_REFRESH; // 19+1 cycles

	oam_temp_full_addr = 6'd0;
	oam_temp_ex_full_addr = 6'b100000;
	oam_db = rendering ? oamtd : oamd;
	oam_ex_db = rendering ? oamxtd : oamxd;
	oam_temp_wren_adj = 0;
	oam_temp_ex_wren = 0;

	case (oam_state)
		STATE_CLEAR: begin
			oam_temp_full_addr = {1'b0, last_cycle[5:1]};
			oam_temp_ex_full_addr = {1'b1, last_cycle[5:1]};
			if (evaluating) begin
				oam_db = 8'hFF;
				oam_ex_db = 8'hFF;
				oam_temp_wren_adj = write_cycle;
				oam_temp_ex_wren = write_cycle;
			end
		end

		STATE_EVAL: begin
			oam_temp_full_addr = {1'b0, oam_temp_slot, (n_ovr || ~oam_temp_wren) ? 2'b00 : oam_addr[1:0]};
			oam_temp_ex_full_addr = {1'b1, oam_temp_slot_ex[2:0], oam_addr_ex[1:0]};

			if (evaluating) begin
				oam_db = ~write_cycle ? oamd : oam_temp_wren ? oamd : oamtd; // FIXME: Odd or even?
				oam_ex_db = oamxd; // FIXME: Odd or even?
				`ifdef EXTRA_SPRITES
				oam_temp_ex_wren = (~ex_ovr && write_cycle);
				`endif
				oam_temp_wren_adj = (oam_temp_wren && write_cycle);
			end
		end

		STATE_FETCH: begin
			oam_temp_full_addr = {1'b0, feed_cnt[5:3], feed_cnt[2:0] > 3 ? 2'b11 : feed_cnt[1:0]};
			oam_temp_ex_full_addr = {1'b1, feed_cnt[5:3] + 1'd1, feed_cnt[1:0]};
		end

		default: begin
			oam_ex_db = rendering ? oamxtd : oamxd;
			oam_db = rendering ? oamtd : oamd;
		end
	endcase
end

dpram #(.widthad_a(6), .width_a(8)) OAM_temp_ram //64 * 8 bits
(
	.clock_a   (clk),
	.address_a (oam_temp_full_addr),
	.data_a    (oam_state == STATE_EVAL ? oam_bus : 8'hFF),
	.wren_a    (oam_temp_wren_adj), // FIXME: Odd or even?
	.q_a       (oamtd),

	.clock_b   (clk),
	.address_b (oam_temp_ex_full_addr),
	.data_b    (oam_state == STATE_EVAL ? oam_ex_data : 8'hFF),
	.wren_b    (oam_temp_ex_wren),
	.q_b       (oamxtd)
);

logic [7:0] oam_db;
logic [7:0] dram_glitch;
logic [7:0] oam_data_delay;

always_ff @(posedge clk) begin :oam_eval
reg [1:0] eval_counter;
reg old_rendering;
reg [8:0] last_y, last_tile, last_attr;

reg overflow;

if (ce) begin
	oam_read_bus <= oam_data;
	spr_overflow <= overflow;

	if (clr_vbl_ovf_sp0) begin
		overflow <= 0;
		spr_overflow <= 0;
	end
end

if (reset) begin
	oam_temp_slot <= 0;
	oam_temp_wren <= 1;
	spr_overflow <= 0;
	n_ovr <= 0;
	repeat_count <= 0;
	sprite0 <= 0;
	sprite0_curr <= 0;
	feed_cnt <= 0;
	overflow <= 0;
	eval_counter <= 0;
	`ifdef EXTRA_SPRITES
	spr_counter <= 0;
	ex_ovr <= 0;
	oam_temp_slot_ex <= 0;
	`endif

end else if (ce2) begin
	// I believe technically oam_data represents the ppu's internal data bus and should be assign to
	// open bus if not driven here, but for now, no behavior relies on this so we can just keep it
	// simple.
	if (rendering || oam_data_read) begin
		oam_data <= oam_db;
		oam_ex_data <= oam_ex_db;
	end

	if (end_of_line) begin
		sprite0 <= sprite0_curr;
		sprite0_curr <= 0;
		oam_temp_slot <= 0;
		oam_temp_wren <= 1;
		n_ovr <= 0;
		repeat_count <= 0;
		feed_cnt <= 0;
		eval_counter <= 0;
		`ifdef EXTRA_SPRITES
		oam_bus_ex <= 32'hFFFFFFFF;
		sprite_data_ex <= '{8'hFF, 8'hFF, 8'hFF, 8'hFF};
		sprite_compare <= '{8'hFF, 8'hFF, 8'hFF, 8'hFF};
		spr_counter <= 0;
		ex_ovr <= 0;
		oam_temp_slot_ex <= 0;
		oam_addr_ex <= 0;
		masked_sprites <= 0;
		`endif
	end

	if (oam_state == STATE_CLEAR) begin               // Initialization state
		if (~write_cycle)
			ram_corruption_data <= oamd;

		`ifdef EXTRA_SPRITES
		// During init, we hunt for the 8th sprite in OAM, so we know where to start for extra sprites
		if (evaluating) begin
			if (~&spr_counter) begin
				oam_addr_ex[7:2] <= oam_addr_ex[7:2] + 1'd1;
				if (scanline[7:0] >= oamxd && scanline[7:0] < oamxd + (obj_size ? 16 : 8))
					spr_counter <= spr_counter + 1'b1;
			end
		end
		`endif
	end

	if (oam_state == STATE_EVAL) begin             // Evaluation State
		if (evaluating) begin
			//On odd cycles, data is read from (primary) OAM
			if (write_cycle) begin
				// This phase has exactly enough cycles to evaluate all 64 sprites if 8 are on the current line,
				// so extra sprite evaluation has to be done seperately.
				`ifdef EXTRA_SPRITES
				if (&spr_counter && ~ex_ovr) begin
					if (~|oam_addr_ex[1:0]) begin
						if (scanline[7:0] >= oamxd &&
							scanline[7:0] < oamxd + (obj_size ? 16 : 8)) begin
							if (oam_temp_slot_ex == 0) begin
								oam_bus_ex[oam_addr_ex[1:0]] <= oamxd;
							end
							if (oam_temp_slot_ex < 8) begin
								{ex_ovr, oam_addr_ex} <= oam_addr_ex + 9'd1;
							end
						end else begin
							{ex_ovr, oam_addr_ex} <= oam_addr_ex + 9'd4;
						end

					end else begin
						if (oam_temp_slot_ex == 0) begin
							oam_bus_ex[oam_addr_ex[1:0]] <= oamxd;
						end
						if (&oam_addr_ex[1:0]) oam_temp_slot_ex <= oam_temp_slot_ex + 1'b1;
						{ex_ovr, oam_addr_ex} <= oam_addr_ex + 9'd1;
					end
				end
				`endif

				if (~n_ovr) begin
					if (~|eval_counter) begin // m is 0
						if (scanline[7:0] >= oam_data && scanline[7:0] < oam_data + (obj_size ? 16 : 8)) begin
							if (~oam_temp_wren)
								overflow <= 1;
							else begin
								sprite_compare[oam_addr[1:0]] <= oam_data;
								if (oam_temp_slot && (sprite_compare[oam_addr[1:0]] == oam_data))
									repeat_count <= repeat_count + 4'd1;
							end
							if (~|oam_addr[7:2])
								sprite0_curr <= 1'b1;
							eval_counter <= eval_counter + 2'd1;
							{n_ovr, oam_addr} <= {1'b0, oam_addr} + 9'd1; // is good, copy
						end else begin
							if (~oam_temp_wren) begin  // Sprite overflow bug emulation
								{n_ovr, oam_addr[7:2]} <= oam_addr[7:2] + 7'd1;
								oam_addr[1:0] <= oam_addr[1:0] + 2'd1;
							end else begin                              // skip to next sprite
								{n_ovr, oam_addr} <= oam_addr + 9'd4;
							end
						end
					end else begin
						eval_counter <= eval_counter + 2'd1;
						{n_ovr, oam_addr} <= {1'b0, oam_addr} + 9'd1;
						if (oam_temp_wren) begin
							sprite_compare[oam_addr[1:0]] <= oam_data;
							if (|oam_temp_slot && ~&oam_addr[1:0] && (sprite_compare[oam_addr[1:0]] == oam_data))
								repeat_count <= repeat_count + 4'd1;

						end
						if (&eval_counter) begin // end of copy
							if (oam_temp_wren) begin
								oam_temp_slot <= oam_temp_slot + 1'b1;
							end else begin
								n_ovr <= 1;
							end

							if (oam_temp_slot == 7)
								oam_temp_wren <= 0;
						end
					end
				end else begin
					oam_addr <= {oam_addr[7:2] + 1'd1, 2'b00};
				end
			end

		end
	end

	if (oam_state == STATE_FETCH) begin
		// OAMADDR is set to 0 during each of ticks 257-320 (the sprite tile loading interval) of the pre-render
		// and visible scanlines.
		`ifdef EXTRA_SPRITES
		if (repeat_count >= 21)
			masked_sprites <= 1;
		`endif

		feed_cnt <= feed_cnt + 1'd1;

		if (rendering) begin
			oam_addr <= 0;
			sprite_data_ex[feed_cnt[1:0]] <= oamxtd;

			if (&feed_cnt[2:0]) begin
				oam_bus_ex <= {sprite_data_ex[3], sprite_data_ex[2], sprite_data_ex[1], sprite_data_ex[0]};
			end
		end
	end
end
	// Writes to OAMDATA during rendering (on the pre-render line and the visible lines 0-239,
	// provided either sprite or background rendering is enabled) do not modify values in OAM,
	// but do perform a glitchy increment of OAMADDR, bumping only the high 6 bits (i.e., it bumps
	// the [n] value in PPU sprite evaluation - it's plausible that it could bump the low bits instead
	// depending on the current status of sprite evaluation). This extends to DMA transfers via OAMDMA,
	// since that uses writes to $2004. For emulation purposes, it is probably best to completely ignore
	// writes during rendering.
	if (oam_data_write) begin
		if (~rendering) begin
			oam_addr <= oam_addr + 1'b1;
		end else begin
			oam_addr <= oam_addr + 8'd4;
		end
	end

	// 2004 write is delayed
	if (oam_addr_write) begin
		oam_addr <= oam_din;
	end
end // End Always

endmodule


// Generates addresses in VRAM where we'll fetch sprite graphics from,
// and populates load, load_in so the SpriteGen can be loaded.
module SpriteAddressGen(
	input         clk,
	input         ce,
	input         enabled,          // If unset, |load| will be all zeros.
	input         obj_size,         // 0: Sprite Height 8, 1: Sprite Height 16.
	input         obj_patt,         // Object pattern table selection
	input   [8:0] scanline,
	input   [2:0] cycle,      // Current load cycle. At #4, first bitmap byte is loaded. At #6, second bitmap byte is.
	input   [7:0] temp,       // Input temp data from SpriteTemp. #0 = Y Coord, #1 = Tile, #2 = Attribs, #3 = X Coord
	input         masked_sprites,
	input   [7:0] vram_data,  // Byte of VRAM in the specified address
	output [12:0] vram_addr,// Low bits of address in VRAM that we'd like to read.
	output  [3:0] load,      // Which subset of load_in that is now valid, will be loaded into SpritesGen.
	output [26:0] load_in,  // Bits to load into SpritesGen.
	output        use_ex
);

logic [7:0] temp_tile, temp_tile_l;    // Holds the tile that we will get
logic [3:0] temp_y, temp_y_l;       // Holds the Y coord (will be swapped based on FlipY).
logic flip_x, flip_y, flip_x_l, flip_y_l;     // If incoming bitmap data needs to be flipped in the X or Y direction.
logic dummy_sprite, dummy_sprite_l; // Set if attrib indicates the sprite is invalid.

wire load_y =    (load_cnt == 0);            // 256 00 N 257 01
wire load_tile = (load_cnt == 1);            // 257 01   258 10 N
wire load_attr = (load_cnt == 2) && enabled; // 258 10 N 259 11
wire load_x =    (load_cnt == 3) && enabled; // 259 11   260 00 S
                                             // 260 00 S 262 01
wire load_pix1 = (cycle == 5) && enabled;    // 261 01   262 10 S
                                             // 262 10 S 263 11
wire load_pix2 = (cycle == 7) && enabled;    // 263 11   264 01 N
logic [2:0] load_cnt;

assign use_ex = ~dummy_sprite && ~load_cnt[2] && ~masked_sprites;

// Flip incoming vram data based on flipx. Zero out the sprite if it's invalid. The bits are already flipped once.
wire [7:0] vram_f =
	dummy_sprite ? 8'd0 :
	!flip_x ? {vram_data[0], vram_data[1], vram_data[2], vram_data[3], vram_data[4], vram_data[5], vram_data[6], vram_data[7]} :
	vram_data;

wire [3:0] y_f = temp_y ^ {flip_y, flip_y, flip_y, flip_y};
assign load = {load_pix1, load_pix2, load_x, load_attr};
assign load_in = {vram_f, vram_f, temp, temp[1:0], temp[5]};

// If $2000.5 = 0, the tile index data is used as usual, and $2000.3
// selects the pattern table to use. If $2000.5 = 1, the MSB of the range
// result value become the LSB of the indexed tile, and the LSB of the tile
// index value determines pattern table selection. The lower 3 bits of the
// range result value are always used as the fine vertical offset into the
// selected pattern.

assign temp_y = (load_y) ? scanline_y[3:0] : temp_y_l;
assign temp_tile = (load_tile) ? temp : temp_tile_l;
assign {flip_y, flip_x, dummy_sprite} = (load_attr) ? {temp[7:6], temp[4]} :
	{flip_y_l, flip_x_l, dummy_sprite_l};

assign vram_addr = {obj_size ? temp_tile[0] :
	obj_patt, temp_tile[7:1], obj_size ? y_f[3] : temp_tile[0], cycle[1], y_f[2:0] };

wire [7:0] scanline_y = scanline[7:0] - temp;

always @(posedge clk) if (ce) begin
	if (enabled)
		load_cnt <= load_cnt + 3'd1;
	else
		load_cnt <= 0;

	if (load_y) temp_y_l <= scanline_y[3:0];
	if (load_tile) temp_tile_l <= temp;
	if (load_attr) {flip_y_l, flip_x_l, dummy_sprite_l} <= {temp[7:6], temp[4]};
end

endmodule  // SpriteAddressGen

`ifdef EXTRA_SPRITES
// Condensed sprite address generator for extra sprites
module SpriteAddressGenEx(
	input clk,
	input ce,
	input enabled,          // If unset, |load| will be all zeros.
	input obj_size,         // 0: Sprite Height 8, 1: Sprite Height 16.
	input obj_patt,         // Object pattern table selection
	input [7:0] scanline,
	input [2:0] cycle,      // Current load cycle. At #4, first bitmap byte is loaded. At #6, second bitmap byte is.
	input [31:0] temp,      // Input temp data from SpriteTemp. #0 = Y Coord, #1 = Tile, #2 = Attribs, #3 = X Coord
	input [7:0] vram_data,  // Byte of VRAM in the specified address
	output [12:0] vram_addr,// Low bits of address in VRAM that we'd like to read.
	output [3:0] load,      // Which subset of load_in that is now valid, will be loaded into SpritesGen.
	output [26:0] load_in,  // Bits to load into SpritesGen.
	output use_ex,          // If extra sprite address should be used
	input masked_sprites
);

// We keep an odd structure here to maintain compatibility with the existing sprite modules
// which are constrained by the behavior of the original system.
wire load_y =    (load_cnt == 0);            // 256 00 N 257 01
wire load_tile = (load_cnt == 1);
wire load_attr = (load_cnt == 2) && enabled;
wire load_x =    (load_cnt == 3) && enabled;
wire load_pix1 = (load_cnt == 5) && enabled;
wire load_pix2 = (load_cnt == 7) && enabled;

reg [7:0] pix1_latch, pix2_latch;

logic [3:0] temp_y, temp_y_l;       // Holds the Y coord (will be swapped based on FlipY).

wire [7:0] scanline_y = scanline[7:0] - temp[7:0];
wire [7:0] tile   = temp[15:8];
wire [7:0] attr   = temp[23:16];
wire [7:0] temp_x = temp[31:24];

wire flip_x = attr[6];
wire flip_y = attr[7];
wire dummy_sprite = attr[4];
logic [2:0] load_cnt;

assign use_ex = ~dummy_sprite && ~cycle[2] && ~masked_sprites;
assign temp_y = (load_y) ? scanline_y[3:0] : temp_y_l;

// Flip incoming vram data based on flipx. Zero out the sprite if it's invalid. The bits are already flipped once.
wire [7:0] vram_f =
	dummy_sprite || masked_sprites ? 8'd0 :
	!flip_x ? {vram_data[0], vram_data[1], vram_data[2], vram_data[3], vram_data[4], vram_data[5], vram_data[6], vram_data[7]} :
	vram_data;

wire [3:0] y_f = temp_y[3:0] ^ {flip_y, flip_y, flip_y, flip_y};
assign load = {load_pix1, load_pix2, load_x, load_attr};
assign load_in = {pix1_latch, pix2_latch, load_temp, load_temp[1:0], load_temp[5]};

logic [7:0] load_temp;
always_comb begin
	load_temp = 8'd0;
	case (load_cnt)
		0: load_temp = temp_y;
		1: load_temp = tile;
		2: load_temp = attr;
		3,4,5,6,7: load_temp = temp_x;
	endcase
end

// If $2000.5 = 0, the tile index data is used as usual, and $2000.3
// selects the pattern table to use. If $2000.5 = 1, the MSB of the range
// result value become the LSB of the indexed tile, and the LSB of the tile
// index value determines pattern table selection. The lower 3 bits of the
// range result value are always used as the fine vertical offset into the
// selected pattern.
assign vram_addr = {obj_size ? tile[0] : obj_patt,
	tile[7:1], obj_size ? y_f[3] : tile[0], cycle[1], y_f[2:0] };
always @(posedge clk) if (ce) begin
	if (enabled)
		load_cnt <= load_cnt + 3'd1;
	else
		load_cnt <= 0;

	if (load_y) temp_y_l <= scanline_y[3:0];
	if (load_tile) pix1_latch <= vram_f;
	if (load_x) pix2_latch <= vram_f;
end

endmodule  // SpriteAddressGenEx
`endif

module BgPainter(
	input clk,
	input ce,
	input clear,
	input enable,             // Shift registers activated
	input [2:0] cycle,
	input [2:0] fine_x_scroll,
	input [14:0] vram_v,
	output [7:0] name_table,  // VRAM name table to read next.
	input [7:0] vram_data,
	output [3:0] pixel
);

reg [15:0] playfield_pipe_1;       // Name table pixel pipeline #1
reg [15:0] playfield_pipe_2;       // Name table pixel pipeline #2
reg [8:0]  playfield_pipe_3;       // Attribute table pixel pipe #1
reg [8:0]  playfield_pipe_4;       // Attribute table pixel pipe #2
reg [7:0] current_name_table;      // Holds the current name table byte
reg [1:0] current_attribute_table; // Holds the 2 current attribute table bits
reg [7:0] bg0;                     // Pixel data for last loaded background
wire [7:0] bg1 =  vram_data;

initial begin
	playfield_pipe_1 = 0;
	playfield_pipe_2 = 0;
	playfield_pipe_3 = 0;
	playfield_pipe_4 = 0;
	current_name_table = 0;
	current_attribute_table = 0;
	bg0 = 0;
end

always @(posedge clk) if (ce) begin
	if (enable) begin
		case (cycle[2:0])
			1: current_name_table <= vram_data;
			3: current_attribute_table <=
				(!vram_v[1] && !vram_v[6]) ? vram_data[1:0] :
				( vram_v[1] && !vram_v[6]) ? vram_data[3:2] :
				(!vram_v[1] &&  vram_v[6]) ? vram_data[5:4] :
				vram_data[7:6];

			5: bg0 <= vram_data; // Pattern table bitmap #0
			//7: bg1 <= vram_data; // Pattern table bitmap #1
		endcase
		playfield_pipe_1[14:0] <= playfield_pipe_1[15:1];
		playfield_pipe_2[14:0] <= playfield_pipe_2[15:1];
		playfield_pipe_3[7:0] <= playfield_pipe_3[8:1];
		playfield_pipe_4[7:0] <= playfield_pipe_4[8:1];
		// Load the new values into the shift registers at the last pixel.
		if (cycle[2:0] == 7) begin
			playfield_pipe_1[15:8] <= {bg0[0], bg0[1], bg0[2], bg0[3], bg0[4], bg0[5], bg0[6], bg0[7]};
			playfield_pipe_2[15:8] <= {bg1[0], bg1[1], bg1[2], bg1[3], bg1[4], bg1[5], bg1[6], bg1[7]};
			playfield_pipe_3[8] <= current_attribute_table[0];
			playfield_pipe_4[8] <= current_attribute_table[1];
		end
	end

	if (clear) begin
		playfield_pipe_1 <= 0;
		playfield_pipe_2 <= 0;
		playfield_pipe_3 <= 0;
		playfield_pipe_4 <= 0;
		current_name_table <= 0;
		current_attribute_table <= 0;
		bg0 <= 0;
	end

end

assign name_table = current_name_table;

wire [3:0] i = {1'b0, fine_x_scroll};

assign pixel = {playfield_pipe_4[i], playfield_pipe_3[i], playfield_pipe_2[i], playfield_pipe_1[i]};

endmodule  // BgPainter


module PixelMuxer(
	input  logic [8:0] cycle,
	input  logic [3:0] bg,
	input  logic [3:0] obj,
	input  logic       obj_prio,
	output logic [4:0] out,
	output logic       is_obj
);

wire bg_valid = |bg[1:0];
wire obj_valid = |obj[1:0];

assign is_obj = obj_valid && ~(obj_prio && bg_valid);
assign out = (bg_valid | obj_valid) ? (is_obj ? {1'b1, obj} : {1'b0, bg}) : 5'd0;

endmodule


module PaletteRam
(
	input clk,
	input ce,
	input [4:0] addr,
	input [5:0] din,
	output [5:0] dout,
	input write_ce,
	input reset
);

logic [4:0] addr_clipped;

assign addr_clipped = |addr[1:0] ? addr : {1'b0, addr[3:0]};

// TODO: Make mif of this
// logic [5:0] palette[32] = '{
// 	6'h00, 6'h01, 6'h00, 6'h01,
// 	6'h00, 6'h02, 6'h02, 6'h0D,
// 	6'h08, 6'h10, 6'h08, 6'h24,
// 	6'h00, 6'h00, 6'h04, 6'h2C,
// 	6'h09, 6'h01, 6'h34, 6'h03,
// 	6'h00, 6'h04, 6'h00, 6'h14,
// 	6'h08, 6'h3A, 6'h00, 6'h02,
// 	6'h00, 6'h20, 6'h2C, 6'h08
// };


spram #(.addr_width(5), .data_width(6)) palette_ram
(
	.clock   (clk),
	.address (reset ? 5'd0 : addr_clipped),
	.data    (reset ? 6'd0 : din),
	.enable  (ce),
	.wren    (write_ce | reset),
	.q       (dout)
);

endmodule  // PaletteRam


//********************************************************************************//
//*******************************  PPU  ******************************************//
//********************************************************************************//


module PPU(
	// Physical pins
	input  logic        clk,              // CORE clock
	input  logic        CS_n,             // Chip Select, defined as phi2 is high && address is in the PPU range
	input  logic        RESET,            // input clock  21.48 MHz / 4. 1 clock cycle = 1 pixel
	input  logic  [7:0] DIN,              // input data from cpu bus
	input  logic  [7:0] VRAM_DIN,         // ppu data, not conflated with ppu_address in our model
	input  logic  [2:0] AIN,              // input address from CPU
	input  logic        RW,               // Read = high, write = low
	input  logic  [3:0] EXT_IN,           // EXT pins input
	output logic        INT_n,            // one while inside vblank
	output logic  [5:0] COLOR,            // output color value, one pixel outputted every clock, replaces composite pins
	output logic        VRAM_R,           // read from vram active
	output logic        VRAM_W,           // write to vram active
	output logic [13:0] VRAM_AB,          // vram address, not conflated with data in our model
	output logic  [7:0] DOUT,             // output data to CPU bus
	output logic  [7:0] VRAM_DOUT,        // ppu data, not conflated with ppu_address in our model
	output logic  [3:0] EXT_OUT,          // EXT output
	output logic        ALE,              // Address Latch Enable, used to deal with the shared ppu_ab and ppu_db

	// Abstract pins
	input  logic        EXTRA_SPRITES,
	input  logic  [1:0] MASK,
	input  logic        CE,               // Clock enable to reduce FPGA timing stress
	input  logic        CE2,              // represents pclk1
	input  logic  [1:0] SYS_TYPE,         // System type. 0 = NTSC 1 = PAL 2 = Dendy 3 = Vs.
	output logic        VRAM_R_EX,        // use extra sprite address
	output logic [13:0] VRAM_A_EX,        // vram address for extra sprites
	output logic  [8:0] SCANLINE,
	output logic  [8:0] CYCLE,
	output logic  [2:0] EMPHASIS,
	output logic        SHORT_FRAME,
	output logic [19:0] mapper_ppu_flags

	// Missing pins
	// VID - Represented as Color and Emphasis outputs
);

// Persistant State

// These are stored in control register 0
logic obj_patt; // Object pattern table
logic bg_patt;  // Background pattern table
logic obj_size; // 1 if sprites are 16 pixels high, else 0.
logic vbl_enable;  // Enable VBL flag
logic enable_playfield;
logic enable_objects;

// These are stored in control register 1
logic grayscale; // Disable color burst
logic playfield_clip;     // 0: Left side 8 pixels playfield clipping
logic object_clip;        // 0: Left side 8 pixels object clipping

logic HVTog;
logic sprite0_hit_bg;            // True if sprite#0 has collided with the BG in the last frame.

// Ephemeral state
logic [8:0] last_cycle;
logic [7:0] vram_latch;
logic [7:0] delay_2001, latch_2001;
logic [7:0] delay_2000, latch_2000;
logic [5:0] color1;
logic [5:0] color2;
logic [5:0] color3;
logic [5:0] color_pipe[4];
logic [7:0] latched_dout;
logic refresh_high, refresh_low;
logic read_old;
logic write_old;

logic load_sprite;
logic skipped;
logic ale_trig;
logic hv_latch;

logic [7:0] oam_read_bus;

logic [7:0] bg_name_table;
logic [3:0] bg_pixel_noblank;

logic [31:0] oam_bus_ex;
logic masked_sprites;
logic [7:0] oam_bus;
logic sprite_overflow;
logic obj0_on_line; // True if sprite#0 is included on the current line
logic [12:0] sprite_vram_addr_ex;
logic [3:0] spriteset_load_ex;
logic [26:0] spriteset_load_in_ex;
logic use_ex;
logic master_mode;
logic show_bg;
logic [3:0] bg_pixel;
logic show_obj;
logic [4:0] obj_pixel;
logic [4:0] pixel;
logic vram_r_ppudata;
logic [4:0] pram_addr;
logic palette_write;
logic [23:0] decay_high;
logic [23:0] decay_low;
logic addr_inc;
logic held_reset;
logic mask_right;
logic vbl_flag;
logic pal_mask;
logic read_ce;
logic write_ce;
logic use_extra_sprites;
logic is_rendering_delayed;

// Continuous Logic
logic read;
logic write;
logic pclk0, pclk1;
logic [13:0] vram_a;
logic end_of_line;         // At the last pixel of a line
logic at_last_cycle_group; // At the very last cycle group of the scan line.
logic exiting_vblank;      // At the very last cycle of the vblank
logic entering_vblank;     //
logic is_pre_render;       // True while we're on the pre render scanline
logic is_visible;
logic is_rendering;
logic rendering_enabled;   // = enable_objects | enable_playfield;
logic [14:0] vram_v;
logic [2:0] fine_x_scroll;
logic is_pal_address; // Set to true if the current ppu_addr pointer points into palette ram.
logic clr_vbl_ovf_sp0;
logic [4:0] obj_pixel_noblank;
logic [12:0] sprite_vram_addr;
logic is_obj0_pixel;            // True if obj_pixel originates from sprite0.
logic [3:0] spriteset_load;     // Which subset of the |load_in| to load into SpriteSet
logic [26:0] spriteset_load_in; // Bits to load into SpriteSet
logic auto_mask;
logic mask_left;
logic mask_pal;
logic clip_area;
logic spr_enabled;
logic bgp_en;

// Reads and Writes
assign read = RW & ~CS_n;
assign write = ~RW & ~CS_n;
assign write_ce = write & ~write_old;
assign read_ce = read & ~read_old;

// Palette and VRAM
assign is_pal_address = &vram_v[13:8];
assign palette_write = write_ce && (AIN == 7) && is_pal_address;
assign pram_addr = is_rendering ? pixel : (is_pal_address ? vram_v[4:0] : (master_mode ? 5'd0 : {1'd0, EXT_IN}));
assign vram_r_ppudata = read && (AIN == 7);

// Colors and Masking
assign show_obj = (object_clip || ~clip_area) && enable_objects;
assign obj_pixel = {obj_pixel_noblank[4:2], show_obj ? obj_pixel_noblank[1:0] : 2'b0};
assign show_bg = (playfield_clip || ~clip_area) && enable_playfield;
assign bg_pixel = {bg_pixel_noblank[3:2], show_bg ? bg_pixel_noblank[1:0] : 2'd00};
assign clip_area = ~|CYCLE[8:3];
assign pal_mask = ~|SCANLINE || CYCLE < 2 || CYCLE > 253;
assign auto_mask = (MASK == 2'b11) && ~object_clip && ~playfield_clip;
assign mask_left = clip_area && ((|MASK && ~&MASK) || auto_mask);
assign mask_right = CYCLE > 247 && MASK == 2'b10;
assign mask_pal = (|SYS_TYPE && pal_mask); // PAL/Dendy masks scanline 0 and 2 pixels on each side with black.
assign color2 = (mask_right | mask_left | mask_pal) ? 6'h0E : color3;
assign color1 = (grayscale ? {color_pipe[1][5:4], 4'b0} : color_pipe[1]);

// Extra Sprites
`ifdef EXTRA_SPRITES
assign use_extra_sprites = EXTRA_SPRITES;
`else
assign use_ex = 0;
assign use_extra_sprites = 0;
assign sprite_vram_addr_ex = 0;
`endif

// Output Pins
assign INT_n = ~(vbl_flag && vbl_enable);
assign EXT_OUT = master_mode ? pram_addr[3:0] : EXT_IN;
assign DOUT = latched_dout;
assign VRAM_W = write && (AIN == 7) && !is_pal_address && !is_rendering;
assign VRAM_DOUT = DIN;
assign VRAM_R = vram_r_ppudata || (is_rendering && CYCLE[0]);
assign ALE = is_rendering ? ~CYCLE[0] : ((read_ce || write_ce) && AIN == 7);
assign VRAM_AB = vram_a;
assign VRAM_A_EX = {1'b0, sprite_vram_addr_ex};
assign COLOR = color1;

assign mapper_ppu_flags = {SCANLINE, CYCLE, obj_size, is_rendering};

// VRAM Address
always_comb begin
	if (~is_rendering) begin
		vram_a = vram_v[13:0];
		VRAM_R_EX = 0;
	end else begin
		if (load_sprite)
			VRAM_R_EX = use_ex && EXTRA_SPRITES;
		else
			VRAM_R_EX = 0;

		if (CYCLE[2:1] == 0 || CYCLE >= 338)
			vram_a = {2'b10, vram_v[11:0]};                                     // Name Table
		else if (CYCLE[2:1] == 1)
			vram_a = {2'b10, vram_v[11:10], 4'b1111, vram_v[9:7], vram_v[4:2]}; // Attribute table
		else if (load_sprite)
			vram_a = {1'b0, sprite_vram_addr};                                  // Sprite data
		else
			vram_a = {1'b0, bg_patt, bg_name_table, CYCLE[1], vram_v[14:12]};   // Pattern table
	end
end

// After spending a few sultry afternoons with visual 2c02, it seems that writes to the PPU follow a
// pattern most of the time. Read and Write are almost always goverened by three inputs: The cpu's
// read-or-write signal, the CE signal (called CS here) which is defined as phi2 AND the cpu address
// is in ppu range, and lastly by the lowest three bits of the address bus itself. In practice what
// this means is that when (write & phi2) are true, the CPU latches to an internal register, but the
// rest of the chip doesn't see this yet. When phi2 goes low, finally the chip reconnects the
// latching register to the internal wires and the effects of the writes take effect. The exceptions
// to this are Enable NMI, Slave Mode, and Grayscale which appear run wires directly to the latching
// register, and thus take effect as soon as (write & ce) are true. HVTog, 2006 and 2005 writes seem
// to behave the same as described above.

// These three signals tap directly into the latch register and apply instantly
assign vbl_enable = write && AIN == 0 ? DIN[7] : delay_2000[7];
assign master_mode = write && AIN == 0 ? DIN[6] : delay_2000[6];
assign grayscale = write && AIN == 1 ? DIN[0] : delay_2001[0];

// 2000 Latched data, only applies after the write signal goes low
assign addr_inc = ~write ? delay_2000[2] : latch_2000[2];
assign obj_patt = ~write ? delay_2000[3] : latch_2000[3];
assign bg_patt = ~write ? delay_2000[4] : latch_2000[4];
assign obj_size = ~write ? delay_2000[5] : latch_2000[5];

// 2001 Latched data, only applies after the write signal goes low
assign playfield_clip = ~write ? delay_2001[1] : latch_2001[1];
assign object_clip = ~write ? delay_2001[2] : latch_2001[2];
assign enable_playfield = ~write ? delay_2001[3] : latch_2001[3];
assign enable_objects = ~write ? delay_2001[4] : latch_2001[4];

assign EMPHASIS[1:0] = ~write ?
	(|SYS_TYPE ? {delay_2001[5], delay_2001[6]} : delay_2001[6:5]) :
	(|SYS_TYPE ? {latch_2001[5], latch_2001[6]} : latch_2001[6:5]);
assign EMPHASIS[2] = write && AIN == 1 ? DIN[7] : delay_2001[7];


ClockGen clock(
	.clk                 (clk),
	.ce                  (CE),
	.ce2                 (CE2),
	.reset               (RESET),
	.held_reset          (held_reset),
	.sys_type            (SYS_TYPE),
	.rendering_enabled   (rendering_enabled),
	.scanline            (SCANLINE),
	.cycle               (CYCLE),
	.end_of_line         (end_of_line),
	.at_last_cycle_group (at_last_cycle_group),
	.exiting_vblank      (exiting_vblank),
	.entering_vblank     (entering_vblank),
	.is_pre_render       (is_pre_render),
	.is_visible          (is_visible),
	.is_rendering        (is_rendering),
	.short_frame         (SHORT_FRAME),
	.clr_vbl_ovf_sp0     (clr_vbl_ovf_sp0),
	.pclk0               (pclk0),
	.pclk1               (pclk1)
);

VramGen vram_v0(
	.clk                 (clk),
	.reset               (held_reset),
	.ce                  (pclk0),
	.pclk1               (pclk1),
	.ppu_incr            (addr_inc),
	.read_ce             (read_ce),
	.write_ce            (write_ce),
	.is_rendering        (is_rendering),
	.rendering_enabled   (rendering_enabled),
	.ain                 (AIN),
	.din                 (DIN),
	.read                (read),
	.write               (write),
	.is_pre_render       (is_pre_render),
	.cycle               (CYCLE),
	.HVTog               (HVTog),
	.vram_v              (vram_v),
	.fine_x_scroll       (fine_x_scroll)
);

OAMEval spriteeval (
	.clk               (clk),
	.ce                (pclk0),
	.ce2               (pclk1),
	.reset             (RESET),
	.clr_vbl_ovf_sp0   (clr_vbl_ovf_sp0),
	.rendering_enabled (rendering_enabled),
	.is_pre_render     (is_pre_render),
	.end_of_line       (end_of_line),
	.is_visible        (is_visible),
	.obj_size          (obj_size),
	.scanline          (SCANLINE),
	.cycle             (CYCLE),
	.oam_bus           (oam_bus),
	.oam_read_bus      (oam_read_bus),
	.oam_bus_ex        (oam_bus_ex),
	.oam_addr_write    (write_ce && (AIN == 3)),
	.oam_data_write    (write_ce && (AIN == 4)),
	.oam_data_read     (read && (AIN == 4)),
	.oam_din           (DIN),
	.spr_overflow      (sprite_overflow),
	.sprite0           (obj0_on_line),
	.PAL               (SYS_TYPE[0]),
	.masked_sprites    (masked_sprites),
	.sprite_load       (load_sprite)
);

// Between 256..319 (64 cycles), fetches bitmap data for the 8 sprites and fills in the SpriteSet
// so that it can start drawing on the next frame.

assign spr_enabled = is_rendering_delayed && enable_objects;

SpriteAddressGen address_gen(
	.clk       (clk),
	.ce        (pclk0),
	.enabled   (load_sprite),  // Load sprites between 256..319
	.obj_size  (obj_size),
	.scanline  (SCANLINE),
	.obj_patt  (obj_patt),               // Object size and pattern table
	.cycle     (CYCLE[2:0]),             // Cycle counter
	.temp      (spr_enabled ? oam_bus : 8'hFF),                // Info from temp buffer.
	.vram_addr (sprite_vram_addr),       // [out] VRAM Address that we want data from
	.vram_data (VRAM_DIN),               // [in] Data at the specified address
	.load      (spriteset_load),
	.load_in   (spriteset_load_in)       // Which parts of SpriteGen to load
);

`ifdef EXTRA_SPRITES
SpriteAddressGenEx address_gen_ex(
	.clk            (clk),
	.ce             (pclk0),
	.enabled        (load_sprite),  // Load sprites between 256..319
	.obj_size       (obj_size),
	.scanline       (SCANLINE[7:0]),
	.obj_patt       (obj_patt),               // Object size and pattern table
	.cycle          (CYCLE[2:0]),             // Cycle counter
	.temp           (spr_enabled ? oam_bus_ex : 32'hFFFFFFFF),                // Info from temp buffer.
	.vram_addr      (sprite_vram_addr_ex),    // [out] VRAM Address that we want data from
	.vram_data      (VRAM_DIN),               // [in] Data at the specified address
	.load           (spriteset_load_ex),
	.load_in        (spriteset_load_in_ex),    // Which parts of SpriteGen to load
	.use_ex         (use_ex),
	.masked_sprites (masked_sprites)
);
`endif

// Between 0..255 (256 cycles), draws pixels.
// Between 256..319 (64 cycles), will be populated for next line
SpriteSet sprite_gen(
	.clk           (clk),
	.ce            (pclk0),
	.enable        (~CYCLE[8]),
	.load          (spriteset_load),
	.load_in       (spriteset_load_in),
	.load_ex       (spriteset_load_ex),
	.load_in_ex    (spriteset_load_in_ex),
	.bits          (obj_pixel_noblank),
	.is_sprite0    (is_obj0_pixel),
	.extra_sprites (use_extra_sprites)
);

assign bgp_en =  (!CYCLE[8] || (CYCLE >= 320 && !at_last_cycle_group)) &&
	is_rendering_delayed && enable_playfield;

BgPainter bg_painter(
	.clk           (clk),
	.ce            (pclk0),
	.clear         (CYCLE == 319),
	.enable        (bgp_en),
	.cycle         (CYCLE[2:0]),
	.fine_x_scroll (fine_x_scroll),
	.vram_v        (vram_v),
	.name_table    (bg_name_table),
	.vram_data     (VRAM_DIN),
	.pixel         (bg_pixel_noblank)
);

PixelMuxer pixel_muxer(
	.cycle    (CYCLE),
	.bg       (bg_pixel[3:0]),
	.obj      (obj_pixel[3:0]),
	.obj_prio (obj_pixel[4]),
	.out      (pixel)
);

PaletteRam palette_ram(
	.clk        (clk),
	.reset      (RESET),
	.ce         (pclk0),
	.addr       (pram_addr), // Read addr
	.din        (DIN[5:0]),  // Value to write
	.dout       (color3),    // Output color
	.write_ce   (palette_write) // Condition for writing
);



// One cycle after vram_r was asserted, the value is available on the bus. vram read delayed is
// actually read2007_done 2007 reads take two cycles, one for address latch, one for reading. vram
// reads or writes take two PPU cycles. ALE is active when 2007 read or write happens, which latches
// the address. On the next ppu cycle, the data is written or read

assign rendering_enabled = enable_objects | enable_playfield;

always @(posedge clk) begin
	read_old <= read;
	write_old <= write;

	if (refresh_high) begin
		decay_high <= 3221590; // aprox 600ms decay rate
		refresh_high <= 0;
	end

	if (refresh_low) begin
		decay_low <= 3221590;
		refresh_low <= 0;
	end

	if (read && AIN == 2)
		hv_latch <= 0;

	if (write) begin
		case (AIN)
			0: begin // PPU Control Register 1
				delay_2000 <= DIN;
			end

			1: begin // PPU Control Register 2
				delay_2001 <= DIN;
			end

			5, 6: hv_latch <= ~HVTog;
		endcase
	end else begin
		HVTog <= hv_latch;
		latch_2000 <= delay_2000;
		latch_2001 <= delay_2001;
	end

	if (clr_vbl_ovf_sp0) begin
		sprite0_hit_bg <= 0;
	end else if (
		pclk0               &&
		~CYCLE[8]           &&    // X Pixel 0..255
		~&CYCLE[7:0]        &&    // X pixel != 255
		is_visible          &&    // Y Pixel 0..239
		obj0_on_line        &&    // True if sprite#0 is included on the scan line.
		is_obj0_pixel       &&    // True if the pixel came from tempram #0.
		|obj_pixel[1:0]     &&
		|bg_pixel[1:0]) begin     // Background pixel nonzero.
			sprite0_hit_bg <= 1;
	end

	if (pclk0)
		skipped <= SHORT_FRAME;


	if (pclk0) begin
		color_pipe <= '{color2, color_pipe[0], color_pipe[1], color_pipe[2]};
		is_rendering_delayed <= is_rendering;
	end

	if (pclk0) begin
		if (clr_vbl_ovf_sp0)
			vbl_flag <= 0;
		else if (entering_vblank)
			vbl_flag <= 1;
	end

	if (read && AIN == 2)
		vbl_flag <= 0;

	if (vram_r_ppudata) begin
		vram_latch <= VRAM_DIN;
	end

	if (pclk0) begin

		if (decay_high > 0)
			decay_high <= decay_high - 1'b1;
		else
			latched_dout[7:5] <= 3'b000;

		if (decay_low > 0)
			decay_low <= decay_low - 1'b1;
		else
			latched_dout[4:0] <= 5'b00000;
	end

	case (AIN)
		2: begin
			if (read_ce)
				latched_dout[7] <= vbl_flag;
			if (read) begin
				latched_dout[5] <= sprite_overflow;
				if (pclk0) latched_dout[6] <= sprite0_hit_bg;
				refresh_high <= 1'b1;
			end
		end

		4: if (read) begin
			latched_dout <= oam_read_bus;
			refresh_high <= 1'b1;
			refresh_low <= 1'b1;
		end

		7: begin
			if (is_pal_address) begin
				if (read) begin
					latched_dout[5:0] <= color1;
					refresh_low <= 1'b1;
				end
			end else begin
				if (read_ce) begin
					latched_dout <= vram_latch;
					refresh_high <= 1'b1;
					refresh_low <= 1'b1;
				end
			end
		end
	endcase

	if (write) begin
		refresh_high <= 1'b1;
		refresh_low <= 1'b1;
		latched_dout <= DIN;
	end

	if (held_reset) begin
		vbl_flag <= 0;
		delay_2000 <= 8'd0;
		delay_2001 <= 8'd0;
		latch_2000 <= 8'd0;
		latch_2001 <= 8'd0;
		HVTog <= 0;
		hv_latch <= 0;
	end

	if (RESET)
		latched_dout <= 8'd0;


end

endmodule  // PPU