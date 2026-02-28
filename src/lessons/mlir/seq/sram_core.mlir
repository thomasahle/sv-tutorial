// sram_core.sv — rewritten as CIRCT MLIR.
//
// The seq dialect represents sequential (stateful) logic.
// Its key operation is seq.compreg — an abstract D flip-flop:
//
//   %q = seq.compreg %d, %clk : T
//
// This is exactly equivalent to always_ff @(posedge clk) q <= d;
// but expressed as a dataflow edge rather than a procedural statement.
// The "compr" stands for "compiled register": reset handling and
// clock-enable are optional fields added later in the lowering pipeline.
//
// Clocks have their own type: !seq.clock.
// hw.module ports and seq ops use !seq.clock (not i1) for clock signals.
//
// hw + comb + seq dialects work together in the same module.
// hw provides structure, comb provides logic, seq provides state.

hw.module @sram_core(in %clk   : !seq.clock,
                     in %we    : i1,
                     in %addr  : i4,
                     in %wdata : i8,
                     out rdata : i8) {

  // The memory array is represented as a high-level memory abstraction.
  // seq.hlmem lowers to a register array + read/write mux logic later.
  // Syntax: seq.hlmem @name %clk, %rst : <depth x element_type>
  %false = hw.constant false
  %mem = seq.hlmem @sram_core %clk, %false : <16xi8>

  // Write port: store wdata at addr, gated by we.
  seq.write %mem[%addr] %wdata wren %we { latency = 1 } : !seq.hlmem<16xi8>

  // Read port: combinational read (latency 0), then register the result.
  // This gives the 1-cycle read latency you observed in the waveforms.
  %rdata_comb = seq.read %mem[%addr] { latency = 0 } : !seq.hlmem<16xi8>
  %rdata      = seq.compreg %rdata_comb, %clk : i8

  hw.output %rdata : i8
}


// ── Simpler example: a single D flip-flop ────────────────────────────────
//
// seq.compreg %d, %clk : i8
//
// ≡  always_ff @(posedge clk) q <= d;
//
// Optional fields:
//   seq.compreg %d, %clk reset %rst, %rstval : i8   — synchronous reset
//   seq.compreg.ce %d, %clk, %en : i8               — clock enable

hw.module @dff(in %d : i8, in %clk : !seq.clock, out q : i8) {
  %q = seq.compreg %d, %clk : i8
  hw.output %q : i8
}
