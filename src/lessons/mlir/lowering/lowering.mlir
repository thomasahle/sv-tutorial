// The lowering pipeline — before and after.
//
// CIRCT transforms hardware IR through a sequence of passes.
// Each pass lowers one dialect level closer to SystemVerilog text.
//
// ─────────────────────────────────────────────────────────────────────────
// STAGE 1  hw + seq  (what you saw in the previous lesson)
// ─────────────────────────────────────────────────────────────────────────

hw.module @dff_before(in %d : i8, in %clk : !seq.clock, out q : i8) {
  %q = seq.compreg %d, %clk : i8
  hw.output %q : i8
}


// ─────────────────────────────────────────────────────────────────────────
// STAGE 2  sv dialect  (after LowerSeqToSV pass)
//
// seq.compreg is replaced by:
//   • sv.reg   — declares a SystemVerilog reg variable
//   • sv.always — the procedural always @(posedge clk) block
//   • sv.passign — non-blocking assignment inside the always block
//   • sv.read_inout — read back the reg's current value
// ─────────────────────────────────────────────────────────────────────────

hw.module @dff_after(in %d : i8, in %clk : i1, out q : i8) {
  %q_reg = sv.reg name "q" : !hw.inout<i8>

  sv.always posedge %clk {
    sv.passign %q_reg, %d : i8
  }

  %q = sv.read_inout %q_reg : !hw.inout<i8>
  hw.output %q : i8
}


// ─────────────────────────────────────────────────────────────────────────
// STAGE 3  SystemVerilog text  (after ExportVerilog pass)
//
// The sv dialect is printed directly as text.  The output for dff_after is:
//
//   module dff_after(input  [7:0] d,
//                    input        clk,
//                    output [7:0] q);
//     reg [7:0] q;
//     always @(posedge clk)
//       q <= d;
//   endmodule
// ─────────────────────────────────────────────────────────────────────────


// ─────────────────────────────────────────────────────────────────────────
// BONUS: the formal verification path (what circt-bmc does)
//
// Instead of going to sv + ExportVerilog, circt-bmc takes the
// hw + comb + seq IR and lowers it to SMT (Satisfiability Modulo Theories):
//
//   hw.module + verif.assert
//        ↓  LowerHWtoBMC
//   verif.bmc { ... }
//        ↓  LowerBMCToSMT
//   SMT operations (smt.forall, smt.assert, ...)
//        ↓  ExportSMTLIB
//   SMTLIB text  →  Z3 solver  →  sat / unsat
//
// This is why circt-bmc can exhaustively check all input combinations
// rather than just the ones your testbench happened to try.
// ─────────────────────────────────────────────────────────────────────────
