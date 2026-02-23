const parts = [
  // ─────────────────────────────────────────────────────────────────────────
  //  PART 1: SystemVerilog Basics
  // ─────────────────────────────────────────────────────────────────────────
  {
    title: 'SystemVerilog Basics',
    chapters: [
      // ── Chapter 1: Introduction ──────────────────────────────────────────
      {
        title: 'Introduction',
        lessons: [
          {
            slug: 'sv/welcome',
            title: 'Welcome',
            waveform: 'off',
            focus: '/src/top.sv',
            html: `
              <p>Welcome to the interactive SystemVerilog tutorial — a hands-on guide to the hardware description and verification language used throughout the industry.</p>
              <p><strong>Part 1 — SystemVerilog Basics</strong> covers the building blocks of synthesisable RTL: modules and ports, combinational logic with <code>always_comb</code>, sequential logic with <code>always_ff</code>, parameterized modules, and state machines.</p>
              <p><strong>Part 2 — SystemVerilog Assertions</strong> covers formal and simulation-based verification: immediate and concurrent assertions, clock-delay sequences, implication operators, sampled-value functions, coverage, and advanced property techniques.</p>
              <p>Every lesson has starter code in the editor on the right. Edit it, click <strong>Run</strong> to execute, and click <strong>Solve</strong> to reveal the answer.</p>
              <blockquote><p>Prior experience with digital logic (flip-flops, gates, clocks) is assumed. Experience with another HDL is helpful but not required.</p></blockquote>
              <p>The simplest SystemVerilog program is a <code>module</code> with an <code>initial</code> block. Edit the message and click Run to try it.</p>
            `,
            files: {
              a: {
                '/src/top.sv': 'module top;\n  initial begin\n    $display("hello, sv tutorial");\n  end\nendmodule\n'
              },
              b: {}
            }
          },
          {
            slug: 'sv/modules-and-ports',
            title: 'Modules and Ports',
            waveform: 'optional',
            focus: '/src/adder.sv',
            html: `
              <p>Modules communicate through <strong>ports</strong>. Each port has a direction (<code>input</code>, <code>output</code>, or <code>inout</code>) and a type.</p>
              <p>The most common type is <code>logic</code> — a 4-state value that can be <code>0</code>, <code>1</code>, <code>X</code> (unknown), or <code>Z</code> (high-impedance). Vectors use a range: <code>logic [7:0]</code> is 8 bits wide.</p>
              <p>Combinational logic can be driven with a continuous <code>assign</code> statement. Open <code>adder.sv</code> and add the missing line:</p>
              <pre>assign sum = a + b;</pre>
            `,
            files: {
              a: {
                '/src/adder.sv': 'module adder(\n  input  logic [7:0] a,\n  input  logic [7:0] b,\n  output logic [7:0] sum\n);\n  // TODO: assign sum = a + b;\nendmodule\n',
                '/src/tb.sv': "module tb;\n  logic [7:0] a, b, sum;\n  adder dut(.a(a), .b(b), .sum(sum));\n  initial begin\n    a = 8'd10; b = 8'd32;\n    #1 $display(\"sum = %0d\", sum);\n  end\nendmodule\n"
              },
              b: {
                '/src/adder.sv': 'module adder(\n  input  logic [7:0] a,\n  input  logic [7:0] b,\n  output logic [7:0] sum\n);\n  assign sum = a + b;\nendmodule\n'
              }
            }
          }
        ]
      },
      // ── Chapter 2: Combinational Logic ───────────────────────────────────
      {
        title: 'Combinational Logic',
        lessons: [
          {
            slug: 'sv/always-comb',
            title: 'always_comb and case',
            waveform: 'optional',
            focus: '/src/mux.sv',
            html: `
              <p>An <code>always_comb</code> block models combinational logic. It re-evaluates automatically whenever any of its inputs change — no sensitivity list needed.</p>
              <p>Inside it you can use procedural statements like <code>if</code> and <code>case</code>. The <code>case</code> statement is often cleaner than a chain of <code>if-else</code> for multi-way selection.</p>
              <p>Open <code>mux.sv</code> and fill in the four <code>case</code> branches to build a 4-to-1 multiplexer:</p>
              <pre>case (sel)
  2'b00: y = a;
  2'b01: y = b;
  2'b10: y = c;
  2'b11: y = d;
endcase</pre>
            `,
            files: {
              a: {
                '/src/mux.sv': "module mux4 #(parameter W = 8) (\n  input  logic [1:0]   sel,\n  input  logic [W-1:0] a, b, c, d,\n  output logic [W-1:0] y\n);\n  always_comb begin\n    case (sel)\n      // TODO: four cases mapping sel to a/b/c/d\n    endcase\n  end\nendmodule\n",
                '/src/tb.sv': "module tb;\n  logic [1:0]  sel;\n  logic [7:0]  a=8'hAA, b=8'hBB, c=8'hCC, d=8'hDD, y;\n  mux4 dut(.sel,.a,.b,.c,.d,.y);\n  initial begin\n    sel=0; #1 $display(\"sel=0 y=%0h\",y);\n    sel=1; #1 $display(\"sel=1 y=%0h\",y);\n    sel=2; #1 $display(\"sel=2 y=%0h\",y);\n    sel=3; #1 $display(\"sel=3 y=%0h\",y);\n  end\nendmodule\n"
              },
              b: {
                '/src/mux.sv': "module mux4 #(parameter W = 8) (\n  input  logic [1:0]   sel,\n  input  logic [W-1:0] a, b, c, d,\n  output logic [W-1:0] y\n);\n  always_comb begin\n    case (sel)\n      2'b00: y = a;\n      2'b01: y = b;\n      2'b10: y = c;\n      2'b11: y = d;\n    endcase\n  end\nendmodule\n"
              }
            }
          },
          {
            slug: 'sv/priority-enc',
            title: 'Priority Encoder',
            waveform: 'optional',
            focus: '/src/priority_enc.sv',
            html: `
              <p><code>casez</code> treats <code>?</code> as a don't-care bit, making it ideal for priority logic where only the <em>highest-set</em> bit matters.</p>
              <p>Open <code>priority_enc.sv</code> and add four <code>casez</code> branches. The highest-index asserted bit in <code>req</code> wins. If no bit is set, output <code>valid = 0</code>.</p>
              <pre>casez (req)
  4'b1???: begin grant = 2'd3; valid = 1'b1; end
  4'b01??: begin grant = 2'd2; valid = 1'b1; end
  ...
endcase</pre>
              <blockquote><p>Always-combinational blocks should have a <strong>default assignment</strong> before the <code>casez</code> to avoid unintended latches if no branch matches.</p></blockquote>
            `,
            files: {
              a: {
                '/src/priority_enc.sv': "module priority_enc (\n  input  logic [3:0] req,\n  output logic [1:0] grant,\n  output logic       valid\n);\n  always_comb begin\n    grant = 2'd0;\n    valid = 1'b0;\n    casez (req)\n      // TODO: four casez branches, highest index wins\n    endcase\n  end\nendmodule\n",
                '/src/tb.sv': "module tb;\n  logic [3:0] req;\n  logic [1:0] grant;\n  logic       valid;\n  priority_enc dut(.req,.grant,.valid);\n  initial begin\n    req=4'b0000; #1 $display(\"req=%b grant=%0d valid=%b\",req,grant,valid);\n    req=4'b0001; #1 $display(\"req=%b grant=%0d valid=%b\",req,grant,valid);\n    req=4'b0110; #1 $display(\"req=%b grant=%0d valid=%b\",req,grant,valid);\n    req=4'b1010; #1 $display(\"req=%b grant=%0d valid=%b\",req,grant,valid);\n  end\nendmodule\n"
              },
              b: {
                '/src/priority_enc.sv': "module priority_enc (\n  input  logic [3:0] req,\n  output logic [1:0] grant,\n  output logic       valid\n);\n  always_comb begin\n    grant = 2'd0;\n    valid = 1'b0;\n    casez (req)\n      4'b1???: begin grant = 2'd3; valid = 1'b1; end\n      4'b01??: begin grant = 2'd2; valid = 1'b1; end\n      4'b001?: begin grant = 2'd1; valid = 1'b1; end\n      4'b0001: begin grant = 2'd0; valid = 1'b1; end\n    endcase\n  end\nendmodule\n"
              }
            }
          }
        ]
      },
      // ── Chapter 3: Sequential Logic ───────────────────────────────────────
      {
        title: 'Sequential Logic',
        lessons: [
          {
            slug: 'sv/always-ff',
            title: 'Flip-Flops with always_ff',
            waveform: 'optional',
            focus: '/src/dff.sv',
            html: `
              <p><code>always_ff</code> models edge-triggered sequential logic. Unlike <code>always_comb</code>, it only updates when a clock edge occurs.</p>
              <p>Use <strong>non-blocking assignment</strong> (<code>&lt;=</code>) inside <code>always_ff</code>. All right-hand sides are evaluated first, then all assignments happen simultaneously at the clock edge — this prevents race conditions.</p>
              <p>Open <code>dff.sv</code> and implement the flip-flop body:</p>
              <pre>always_ff @(posedge clk) begin
  if (!rst_n) q &lt;= 1'b0;
  else        q &lt;= d;
end</pre>
              <blockquote><p>Active-low reset (<code>rst_n</code>) is conventional in RTL: the signal name ends in <code>_n</code> and asserts at 0.</p></blockquote>
            `,
            files: {
              a: {
                '/src/dff.sv': 'module dff (\n  input  logic clk, rst_n, d,\n  output logic q\n);\n  always_ff @(posedge clk) begin\n    // TODO: if (!rst_n) q <= 0; else q <= d;\n  end\nendmodule\n',
                '/src/tb.sv': "module tb;\n  logic clk=0, rst_n=0, d=0, q;\n  always #5 clk = ~clk;\n  dff dut(.clk,.rst_n,.d,.q);\n  initial begin\n    @(posedge clk); #1;\n    $display(\"in reset:    q=%b (expect 0)\", q);\n    rst_n=1; d=1; @(posedge clk); #1;\n    $display(\"d=1 clocked: q=%b (expect 1)\", q);\n    d=0; @(posedge clk); #1;\n    $display(\"d=0 clocked: q=%b (expect 0)\", q);\n    $finish;\n  end\nendmodule\n"
              },
              b: {
                '/src/dff.sv': "module dff (\n  input  logic clk, rst_n, d,\n  output logic q\n);\n  always_ff @(posedge clk) begin\n    if (!rst_n) q <= 1'b0;\n    else        q <= d;\n  end\nendmodule\n"
              }
            }
          },
          {
            slug: 'sv/counter',
            title: 'Up-Counter',
            waveform: 'optional',
            focus: '/src/counter.sv',
            html: `
              <p>A counter is the canonical example of sequential logic with state. It uses the same <code>always_ff</code> pattern as a flip-flop, but adds an enable signal and an incrementing expression.</p>
              <p>Open <code>counter.sv</code> and implement an 8-bit up-counter:</p>
              <ul>
                <li>Synchronous reset: when <code>!rst_n</code>, set <code>count</code> to zero</li>
                <li>Count up: when <code>en</code> is high, add 1 each cycle</li>
              </ul>
              <blockquote><p>Notice that <code>else if</code> naturally gives reset higher priority than enable — a common and intentional idiom in RTL.</p></blockquote>
            `,
            files: {
              a: {
                '/src/counter.sv': "module counter (\n  input  logic       clk, rst_n, en,\n  output logic [7:0] count\n);\n  always_ff @(posedge clk) begin\n    // TODO: synchronous reset, then increment when en\n  end\nendmodule\n",
                '/src/tb.sv': "module tb;\n  logic clk=0, rst_n=0, en=0;\n  logic [7:0] count;\n  always #5 clk = ~clk;\n  counter dut(.clk,.rst_n,.en,.count);\n  initial begin\n    @(posedge clk); rst_n=1; en=1;\n    repeat(5) @(posedge clk);\n    #1 $display(\"after 5 cycles: %0d (expect 5)\", count);\n    en=0; @(posedge clk); #1;\n    $display(\"after pause:    %0d (expect 5)\", count);\n    rst_n=0; @(posedge clk); #1;\n    $display(\"after reset:    %0d (expect 0)\", count);\n    $finish;\n  end\nendmodule\n"
              },
              b: {
                '/src/counter.sv': "module counter (\n  input  logic       clk, rst_n, en,\n  output logic [7:0] count\n);\n  always_ff @(posedge clk) begin\n    if (!rst_n)  count <= 8'd0;\n    else if (en) count <= count + 8'd1;\n  end\nendmodule\n"
              }
            }
          }
        ]
      },
      // ── Chapter 4: Parameterized Modules ─────────────────────────────────
      {
        title: 'Parameterized Modules',
        lessons: [
          {
            slug: 'sv/parameters',
            title: 'Parameters and localparam',
            waveform: 'optional',
            focus: '/src/counter_n.sv',
            html: `
              <p>Hard-coding a width like <code>[7:0]</code> locks a module to a single configuration. <strong>Parameters</strong> let you write the module once and instantiate it at any width:</p>
              <pre>module counter_n #(parameter int N = 8) (
  input  logic         clk, rst_n, en,
  output logic [N-1:0] count
);</pre>
              <p>Override the default at instantiation time with the <code>#( )</code> syntax:</p>
              <pre>counter_n #(.N(4)) u4(.clk, .rst_n, .en, .count(cnt4));</pre>
              <p>A <strong>localparam</strong> is a constant derived inside the module that cannot be overridden:</p>
              <pre>localparam int MAX = (1 &lt;&lt; N) - 1;</pre>
              <p>Open <code>counter_n.sv</code>. Add <code>#(parameter int N = 8)</code> to the header, replace the hardcoded <code>[7:0]</code> with <code>[N-1:0]</code>, and add a <code>localparam MAX</code>.</p>
              <blockquote><p>Always use <code>localparam</code> for values derived from a parameter — it signals to readers that the constant is not an interface boundary and cannot be changed from outside the module.</p></blockquote>
            `,
            files: {
              a: {
                '/src/counter_n.sv': "module counter_n (\n  // TODO: add #(parameter int N = 8)\n  input  logic       clk, rst_n, en,\n  output logic [7:0] count  // TODO: change to [N-1:0]\n);\n  // TODO: add localparam int MAX = (1 << N) - 1;\n  always_ff @(posedge clk)\n    if (!rst_n)  count <= '0;\n    else if (en) count <= count + 1'b1;\nendmodule\n",
                '/src/tb.sv': "module tb;\n  logic clk=0, rst_n=0, en=1;\n  logic [7:0] cnt8;\n  always #5 clk = ~clk;\n  counter_n dut(.clk,.rst_n,.en,.count(cnt8));\n  initial begin\n    @(posedge clk); rst_n=1;\n    repeat(5) @(posedge clk);\n    #1 $display(\"after 5 cycles: %0d (expect 5)\", cnt8);\n    $finish;\n  end\nendmodule\n"
              },
              b: {
                '/src/counter_n.sv': "module counter_n #(parameter int N = 8) (\n  input  logic         clk, rst_n, en,\n  output logic [N-1:0] count\n);\n  localparam int MAX = (1 << N) - 1;\n  always_ff @(posedge clk)\n    if (!rst_n)  count <= '0;\n    else if (en) count <= count + 1'b1;\nendmodule\n",
                '/src/tb.sv': "module tb;\n  logic clk=0, rst_n=0, en=1;\n  logic [3:0] cnt4;\n  logic [7:0] cnt8;\n  always #5 clk = ~clk;\n  counter_n #(.N(4)) u4(.clk,.rst_n,.en,.count(cnt4));\n  counter_n #(.N(8)) u8(.clk,.rst_n,.en,.count(cnt8));\n  initial begin\n    @(posedge clk); rst_n=1;\n    repeat(20) @(posedge clk);\n    #1 $display(\"4-bit wraps at 16: %0d\", cnt4);\n    $display(\"8-bit count:        %0d\", cnt8);\n    $finish;\n  end\nendmodule\n"
              }
            }
          }
        ]
      },
      // ── Chapter 5: State Machines ─────────────────────────────────────────
      {
        title: 'State Machines',
        lessons: [
          {
            slug: 'sv/enums',
            title: 'typedef enum',
            waveform: 'optional',
            focus: '/src/status.sv',
            html: `
              <p>Magic numbers in state machines are hard to read and easy to mistype. SystemVerilog <strong>enumerations</strong> give each state a readable name and let the compiler catch invalid assignments:</p>
              <pre>typedef enum logic [1:0] {
  IDLE, RUNNING, DONE, ERROR
} status_t;</pre>
              <p>Declare signals with the enum type and use named constants in <code>case</code> statements:</p>
              <pre>status_t state;
...
case (state)
  IDLE:    if (start) state &lt;= RUNNING;
  RUNNING: if (stop)  state &lt;= DONE;
endcase</pre>
              <p>Open <code>status.sv</code> and fill in the two active <code>case</code> branches using the named constants <code>RUNNING</code> and <code>ERROR</code>.</p>
              <blockquote><p>With <code>unique case</code> or in strict-mode tools, an unhandled enum value raises a warning. Add a <code>default</code> branch to catch any encoding bugs.</p></blockquote>
            `,
            files: {
              a: {
                '/src/status.sv': "typedef enum logic [1:0] { IDLE, RUNNING, DONE, ERROR } status_t;\n\nmodule status_display(\n  input  status_t  st,\n  output logic     active,\n  output logic     err\n);\n  always_comb begin\n    active = 1'b0;\n    err    = 1'b0;\n    case (st)\n      // TODO: RUNNING: active = 1'b1;\n      // TODO: ERROR:   err    = 1'b1;\n      default: ; // all other states: keep defaults\n    endcase\n  end\nendmodule\n",
                '/src/tb.sv': "module tb;\n  status_t st;\n  logic active, err;\n  status_display dut(.st,.active,.err);\n  initial begin\n    st = IDLE;    #1 $display(\"IDLE:    active=%b err=%b\", active, err);\n    st = RUNNING; #1 $display(\"RUNNING: active=%b err=%b\", active, err);\n    st = DONE;    #1 $display(\"DONE:    active=%b err=%b\", active, err);\n    st = ERROR;   #1 $display(\"ERROR:   active=%b err=%b\", active, err);\n  end\nendmodule\n"
              },
              b: {
                '/src/status.sv': "typedef enum logic [1:0] { IDLE, RUNNING, DONE, ERROR } status_t;\n\nmodule status_display(\n  input  status_t  st,\n  output logic     active,\n  output logic     err\n);\n  always_comb begin\n    active = 1'b0;\n    err    = 1'b0;\n    case (st)\n      RUNNING: active = 1'b1;\n      ERROR:   err    = 1'b1;\n      default: ;\n    endcase\n  end\nendmodule\n"
              }
            }
          },
          {
            slug: 'sv/fsm',
            title: 'Two-Always Moore FSM',
            waveform: 'optional',
            focus: '/src/seq_det.sv',
            html: `
              <p>A <strong>Moore FSM</strong> uses two always-blocks: one for the state register, one for combinational next-state and output logic. Keeping them separate makes both halves easier to read and verify:</p>
              <pre>// 1. State register
always_ff @(posedge clk)
  state &lt;= (!rst_n) ? S0 : next;

// 2. Next-state + output (combinational)
always_comb begin
  next = state;  // default: hold
  case (state)
    S0: if (din) next = S1;
    ...
  endcase
end</pre>
              <p>This module detects the sequence <strong>1 → 0 → 1</strong> on serial input <code>din</code>. Open <code>seq_det.sv</code> and fill in the four <code>case</code> branches inside the <code>always_comb</code> block.</p>
              <blockquote><p>The default assignment <code>next = state</code> at the top of the <code>always_comb</code> block means "stay in the current state unless a branch overrides it." This eliminates latches and makes every unspecified transition explicit.</p></blockquote>
            `,
            files: {
              a: {
                '/src/seq_det.sv': "// Detects the sequence: 1 -> 0 -> 1\ntypedef enum logic [1:0] { S0, S1, S2, S3 } state_t;\n\nmodule seq_det (\n  input  logic clk, rst_n, din,\n  output logic detected\n);\n  state_t state, next;\n\n  always_ff @(posedge clk)\n    if (!rst_n) state <= S0;\n    else        state <= next;\n\n  always_comb begin\n    next     = state;  // hold by default\n    detected = 1'b0;\n    case (state)\n      // TODO: S0: next = din ? S1 : S0;\n      // TODO: S1: next = din ? S1 : S2;  (stay on repeated 1)\n      // TODO: S2: next = din ? S3 : S0;  (0->1 matches; 0->0 resets)\n      // TODO: S3: begin detected = 1'b1; next = din ? S1 : S0; end\n      default: next = S0;\n    endcase\n  end\nendmodule\n",
                '/src/tb.sv': "module tb;\n  logic clk=0, rst_n=0, din=0, detected;\n  always #5 clk = ~clk;\n  seq_det dut(.clk,.rst_n,.din,.detected);\n  task automatic send(input logic b);\n    din = b; @(posedge clk); #1;\n  endtask\n  initial begin\n    @(posedge clk); rst_n = 1;\n    send(1); send(0); send(1);\n    $display(\"after 1-0-1: detected=%b (expect 1)\", detected);\n    send(0); send(1); send(0); send(1);\n    $display(\"after 1-0-1: detected=%b (expect 1)\", detected);\n    send(0);\n    $display(\"after extra 0: detected=%b (expect 0)\", detected);\n    $finish;\n  end\nendmodule\n"
              },
              b: {
                '/src/seq_det.sv': "// Detects the sequence: 1 -> 0 -> 1\ntypedef enum logic [1:0] { S0, S1, S2, S3 } state_t;\n\nmodule seq_det (\n  input  logic clk, rst_n, din,\n  output logic detected\n);\n  state_t state, next;\n\n  always_ff @(posedge clk)\n    if (!rst_n) state <= S0;\n    else        state <= next;\n\n  always_comb begin\n    next     = state;\n    detected = 1'b0;\n    case (state)\n      S0: next = din ? S1 : S0;\n      S1: next = din ? S1 : S2;\n      S2: next = din ? S3 : S0;\n      S3: begin detected = 1'b1; next = din ? S1 : S0; end\n      default: next = S0;\n    endcase\n  end\nendmodule\n"
              }
            }
          }
        ]
      }
    ]
  },

  // ─────────────────────────────────────────────────────────────────────────
  //  PART 2: SystemVerilog Assertions
  // ─────────────────────────────────────────────────────────────────────────
  {
    title: 'SystemVerilog Assertions',
    chapters: [
      // ── Chapter 1: Your First Assertion ──────────────────────────────────
      {
        title: 'Your First Assertion',
        lessons: [
          {
            slug: 'sva/immediate-assert',
            title: 'Immediate Assertions',
            waveform: 'required',
            focus: '/src/checker.sv',
            html: `
              <p>An <strong>immediate assertion</strong> is a non-temporal check that lives inside a procedural block. It fires the instant the simulator reaches it — no clock required.</p>
              <pre>assert (expression)
  pass_action;
else
  fail_action;</pre>
              <p>If the expression is <code>0</code>, <code>x</code>, or <code>z</code>, the assertion <strong>fails</strong> and the <code>else</code> branch runs.</p>
              <p>Open <code>checker.sv</code> and add two assertions inside the <code>always @(posedge clk)</code> block:</p>
              <ul>
                <li>Never write when full: <code>assert (!wr_en || !full)</code></li>
                <li>Never read when empty: <code>assert (!rd_en || !empty)</code></li>
              </ul>
              <blockquote><p>Use <code>$error</code> in the else clause for an automatic timestamp and file/line location in the log.</p></blockquote>
            `,
            files: {
              a: {
                '/src/checker.sv': 'module fifo_checker(\n  input logic clk,\n  input logic wr_en, rd_en,\n  input logic full, empty\n);\n  always @(posedge clk) begin\n    // TODO: assert we never write when full\n    // TODO: assert we never read when empty\n  end\nendmodule\n'
              },
              b: {
                '/src/checker.sv': 'module fifo_checker(\n  input logic clk,\n  input logic wr_en, rd_en,\n  input logic full, empty\n);\n  always @(posedge clk) begin\n    assert (!wr_en || !full)\n      else $error("Write to full FIFO!");\n    assert (!rd_en || !empty)\n      else $error("Read from empty FIFO!");\n  end\nendmodule\n'
              }
            }
          },
          {
            slug: 'sva/sequence-basics',
            title: 'Sequences and Properties',
            waveform: 'required',
            focus: '/src/grant_check.sv',
            html: `
              <p>A <strong>concurrent assertion</strong> runs in parallel with the design and samples signals at a clock edge. It consists of three pieces:</p>
              <ol>
                <li>A <strong>sequence</strong> — a temporal pattern using the <code>##</code> clock-delay operator</li>
                <li>A <strong>property</strong> — attaches the sequence to a clock and a trigger condition</li>
                <li>An <strong>assert</strong> — evaluates the property at every clock edge</li>
              </ol>
              <p>Open <code>grant_check.sv</code>. The spec is: <em>when <code>cStart</code> is high, <code>req</code> must be high the same cycle and <code>gnt</code> must be high exactly 2 cycles later.</em></p>
              <p>Fill in the sequence body, the property body, and add the <code>assert property</code> statement.</p>
              <blockquote><p>A property is never evaluated on its own — it must be <strong>asserted</strong>, <strong>covered</strong>, or <strong>assumed</strong>.</p></blockquote>
            `,
            files: {
              a: {
                '/src/grant_check.sv': 'module grant_check(input logic clk, cStart, req, gnt);\n\n  // A sequence is a temporal pattern\n  sequence sr1;\n    // TODO: req ##2 gnt;\n  endsequence\n\n  // A property binds a sequence to a clock and a trigger\n  property pr1;\n    // TODO: @(posedge clk) cStart |-> sr1;\n  endproperty\n\n  // TODO: reqGnt: assert property (pr1);\n\nendmodule\n'
              },
              b: {
                '/src/grant_check.sv': 'module grant_check(input logic clk, cStart, req, gnt);\n\n  sequence sr1;\n    req ##2 gnt;\n  endsequence\n\n  property pr1;\n    @(posedge clk) cStart |-> sr1;\n  endproperty\n\n  reqGnt: assert property (pr1)\n    $display("PASS at %0t", $time);\n  else\n    $display("FAIL at %0t", $time);\n\nendmodule\n'
              }
            }
          }
        ]
      },
      // ── Chapter 2: Clock Delay & Sequences ───────────────────────────────
      {
        title: 'Clock Delay & Sequences',
        lessons: [
          {
            slug: 'sva/clock-delay',
            title: 'Clock Delay ##m and ##[m:n]',
            waveform: 'required',
            focus: '/src/delay_check.sv',
            html: `
              <p>The <strong>clock delay</strong> operator <code>##</code> is what makes sequence expressions temporal. It shifts evaluation forward by one or more clock cycles.</p>
              <ul>
                <li><code>##m</code> — exactly <em>m</em> cycles later</li>
                <li><code>##[m:n]</code> — between <em>m</em> and <em>n</em> cycles later</li>
                <li><code>##[1:$]</code> — one or more cycles (<code>$</code> means unbounded)</li>
              </ul>
              <p>Open <code>delay_check.sv</code>. The spec is: <em>after a memory request (<code>mem_req</code>), the response (<code>mem_ack</code>) must arrive within 2 to 5 clock cycles.</em></p>
              <p>Complete the property body using <code>|-> ##[2:5]</code>.</p>
            `,
            files: {
              a: {
                '/src/delay_check.sv': 'module delay_check(input logic clk, mem_req, mem_ack);\n\n  property mem_latency_p;\n    @(posedge clk)\n      // TODO: mem_req |-> ##[2:5] mem_ack;\n      ;\n  endproperty\n\n  mem_latency_a: assert property (mem_latency_p);\n\nendmodule\n'
              },
              b: {
                '/src/delay_check.sv': 'module delay_check(input logic clk, mem_req, mem_ack);\n\n  property mem_latency_p;\n    @(posedge clk) mem_req |-> ##[2:5] mem_ack;\n  endproperty\n\n  mem_latency_a: assert property (mem_latency_p);\n\nendmodule\n'
              }
            }
          },
          {
            slug: 'sva/consecutive-rep',
            title: 'Consecutive Repetition [*m]',
            waveform: 'required',
            focus: '/src/hold_check.sv',
            html: `
              <p>The <strong>consecutive repetition</strong> operator requires a signal to hold true for a contiguous run of clock cycles:</p>
              <ul>
                <li><code>sig[*m]</code> — exactly <em>m</em> consecutive cycles</li>
                <li><code>sig[*m:n]</code> — between <em>m</em> and <em>n</em> consecutive cycles</li>
                <li><code>sig[*0:$]</code> — zero or more cycles</li>
              </ul>
              <p>For example, <code>start |=> valid[*4]</code> means: after <code>start</code>, <code>valid</code> must be high for 4 cycles in a row.</p>
              <p>Open <code>hold_check.sv</code>. The spec is: <em>after a <code>start</code> pulse, <code>busy</code> must stay high for exactly 3 consecutive cycles.</em></p>
              <p>Complete the property using <code>busy[*3]</code>.</p>
            `,
            files: {
              a: {
                '/src/hold_check.sv': 'module hold_check(input logic clk, start, busy);\n\n  property busy_hold_p;\n    @(posedge clk)\n      // TODO: start |=> busy[*3];\n      ;\n  endproperty\n\n  busy_hold_a: assert property (busy_hold_p);\n\nendmodule\n'
              },
              b: {
                '/src/hold_check.sv': 'module hold_check(input logic clk, start, busy);\n\n  property busy_hold_p;\n    @(posedge clk) start |=> busy[*3];\n  endproperty\n\n  busy_hold_a: assert property (busy_hold_p);\n\nendmodule\n'
              }
            }
          },
          {
            slug: 'sva/nonconsec-rep',
            title: 'Goto Repetition [->m]',
            waveform: 'required',
            focus: '/src/multi_ack.sv',
            html: `
              <p>The <strong>goto repetition</strong> operator <code>[->m]</code> requires a condition to be true exactly <em>m</em> times — but the occurrences do not need to be consecutive. Any number of false cycles may separate them:</p>
              <pre>req |=> ack[->3] ##1 done</pre>
              <p>This reads: after <code>req</code>, wait for <code>ack</code> to go high 3 separate times (non-consecutively), then check that <code>done</code> is high immediately after the third.</p>
              <p>Compare with consecutive repetition: <code>ack[*3]</code> requires 3 cycles in a row, while <code>ack[->3]</code> allows gaps between pulses.</p>
              <p>Open <code>multi_ack.sv</code> and complete the property body using <code>ack[->3] ##1 done</code>.</p>
              <blockquote><p>The related operator <code>[=m]</code> is similar but does not require the sequence to end on the last match — the window can extend further. For most protocol checks, <code>[->m]</code> is what you want.</p></blockquote>
            `,
            files: {
              a: {
                '/src/multi_ack.sv': 'module multi_ack(input logic clk, req, ack, done);\n\n  property three_acks_p;\n    @(posedge clk)\n      // TODO: req |=> ack[->3] ##1 done;\n      ;\n  endproperty\n\n  three_acks_a: assert property (three_acks_p);\n\nendmodule\n'
              },
              b: {
                '/src/multi_ack.sv': 'module multi_ack(input logic clk, req, ack, done);\n\n  property three_acks_p;\n    @(posedge clk) req |=> ack[->3] ##1 done;\n  endproperty\n\n  three_acks_a: assert property (three_acks_p);\n\nendmodule\n'
              }
            }
          }
        ]
      },
      // ── Chapter 3: Properties & Implication ──────────────────────────────
      {
        title: 'Properties & Implication',
        lessons: [
          {
            slug: 'sva/implication',
            title: 'Implication: |-> and |=>',
            waveform: 'required',
            focus: '/src/implication.sv',
            html: `
              <p>The implication operator splits a property into two parts:</p>
              <ul>
                <li>The <strong>antecedent</strong> (left side) — the trigger condition</li>
                <li>The <strong>consequent</strong> (right side) — what must hold after the trigger</li>
              </ul>
              <p>There are two forms. Both say "if the left side matches, then the right side must hold" — they differ only in <em>when</em> the consequent starts:</p>
              <ul>
                <li><code>ant |-> con</code> — <strong>overlapping</strong>: consequent starts at the same cycle as the antecedent match</li>
                <li><code>ant |=> con</code> — <strong>non-overlapping</strong>: consequent starts 1 cycle later (equivalent to <code>|-> ##1</code>)</li>
              </ul>
              <p>Open <code>implication.sv</code> and complete both property bodies.</p>
              <blockquote><p>If the antecedent never matches, the property passes <em>vacuously</em>. Use <code>cover property</code> to confirm the antecedent was actually exercised.</p></blockquote>
            `,
            files: {
              a: {
                '/src/implication.sv': 'module implication_demo(input logic clk, req, ack);\n\n  // Overlapping: ack must be high THE SAME cycle req is high\n  property p_ol;\n    // TODO: @(posedge clk) req |-> ack;\n  endproperty\n\n  // Non-overlapping: ack must be high the NEXT cycle after req\n  property p_nol;\n    // TODO: @(posedge clk) req |=> ack;\n  endproperty\n\n  a_ol:  assert property (p_ol);\n  a_nol: assert property (p_nol);\n\nendmodule\n'
              },
              b: {
                '/src/implication.sv': 'module implication_demo(input logic clk, req, ack);\n\n  property p_ol;\n    @(posedge clk) req |-> ack;\n  endproperty\n\n  property p_nol;\n    @(posedge clk) req |=> ack;\n  endproperty\n\n  a_ol:  assert property (p_ol);\n  a_nol: assert property (p_nol);\n\nendmodule\n'
              }
            }
          },
          {
            slug: 'sva/req-ack',
            title: 'Request / Acknowledge',
            waveform: 'required',
            focus: '/src/req_ack.sv',
            html: `
              <p>The request/acknowledge handshake is one of the most common patterns in RTL interfaces. Asserting it correctly combines clock delay, implication, and edge detection.</p>
              <p>Open <code>req_ack.sv</code>. The spec is: <em>after <code>req</code> rises, <code>ack</code> must go high within 1 to 3 clock cycles.</em></p>
              <p>Complete the property using <code>$rose</code>, <code>|=></code>, and <code>##[0:2]</code>:</p>
              <pre>$rose(req) |=> ##[0:2] ack</pre>
              <blockquote><p><code>$rose(req)</code> is true only when <code>req</code> just transitioned from 0 to 1 — it won't re-trigger while <code>req</code> stays high.</p></blockquote>
            `,
            files: {
              a: {
                '/src/req_ack.sv': 'module req_ack_check(input logic clk, req, ack);\n\n  property req_ack_p;\n    @(posedge clk)\n      // TODO: $rose(req) |=> ##[0:2] ack;\n      ;\n  endproperty\n\n  req_ack_a: assert property (req_ack_p);\n\nendmodule\n'
              },
              b: {
                '/src/req_ack.sv': 'module req_ack_check(input logic clk, req, ack);\n\n  property req_ack_p;\n    @(posedge clk) $rose(req) |=> ##[0:2] ack;\n  endproperty\n\n  req_ack_a: assert property (req_ack_p);\n\nendmodule\n'
              }
            }
          },
          {
            slug: 'sva/disable-iff',
            title: 'disable iff — Reset Handling',
            waveform: 'required',
            focus: '/src/reset_check.sv',
            html: `
              <p>During reset, the design is in an undefined state and assertions will fire spuriously. The <code>disable iff</code> clause suppresses an entire property whenever a condition is true.</p>
              <pre>property p;
  @(posedge clk) disable iff (!rst_n)
    req |=> ack;
endproperty</pre>
              <p>While <code>!rst_n</code> is true, the property evaluates as vacuously true — no failure is reported.</p>
              <p>Open <code>reset_check.sv</code> and add <code>disable iff (!rst_n)</code> to the property, between the clock specification and the implication.</p>
              <blockquote><p><code>disable iff</code> is asynchronous: the property is disabled the moment the condition becomes true, not at the next clock edge.</p></blockquote>
            `,
            files: {
              a: {
                '/src/reset_check.sv': 'module reset_check(\n  input logic clk, rst_n,\n  input logic req, ack\n);\n  property req_ack_p;\n    @(posedge clk)\n      // TODO: add disable iff (!rst_n) before the implication\n      req |=> ack;\n  endproperty\n\n  req_ack_a: assert property (req_ack_p);\n\nendmodule\n'
              },
              b: {
                '/src/reset_check.sv': 'module reset_check(\n  input logic clk, rst_n,\n  input logic req, ack\n);\n  property req_ack_p;\n    @(posedge clk) disable iff (!rst_n)\n      req |=> ack;\n  endproperty\n\n  req_ack_a: assert property (req_ack_p);\n\nendmodule\n'
              }
            }
          }
        ]
      },
      // ── Chapter 4: Sampled Value Functions ───────────────────────────────
      {
        title: 'Sampled Value Functions',
        lessons: [
          {
            slug: 'sva/rose-fell',
            title: '$rose and $fell',
            waveform: 'required',
            focus: '/src/edge_check.sv',
            html: `
              <p>Sampled value functions compare a signal's value at the current clock edge against the previous one:</p>
              <ul>
                <li><code>$rose(sig)</code> — true when <code>sig</code> just transitioned <code>0&rarr;1</code></li>
                <li><code>$fell(sig)</code> — true when <code>sig</code> just transitioned <code>1&rarr;0</code></li>
              </ul>
              <p>These are more precise than a bare level check: <code>$rose(req)</code> triggers once per rising edge, not on every cycle that <code>req</code> stays high.</p>
              <p>Open <code>edge_check.sv</code>. The spec is: <em>when chip-select <code>cs_n</code> falls (goes active-low), <code>ack</code> must rise within 1–2 clock cycles.</em></p>
              <p>Complete the property using <code>$fell(cs_n) |=> ##[0:1] $rose(ack)</code>.</p>
            `,
            files: {
              a: {
                '/src/edge_check.sv': 'module edge_check(input logic clk, cs_n, ack);\n\n  property cs_ack_p;\n    @(posedge clk)\n      // TODO: $fell(cs_n) |=> ##[0:1] $rose(ack);\n      ;\n  endproperty\n\n  cs_ack_a: assert property (cs_ack_p);\n\nendmodule\n'
              },
              b: {
                '/src/edge_check.sv': 'module edge_check(input logic clk, cs_n, ack);\n\n  property cs_ack_p;\n    @(posedge clk) $fell(cs_n) |=> ##[0:1] $rose(ack);\n  endproperty\n\n  cs_ack_a: assert property (cs_ack_p);\n\nendmodule\n'
              }
            }
          },
          {
            slug: 'sva/stable-past',
            title: '$stable and $past',
            waveform: 'required',
            focus: '/src/stable_check.sv',
            html: `
              <p>Two more sampled value functions for tracking signal history:</p>
              <ul>
                <li><code>$stable(sig)</code> — true when <code>sig</code> did <em>not</em> change between the previous and current clock edge</li>
                <li><code>$past(sig)</code> — the value of <code>sig</code> from exactly 1 cycle ago; <code>$past(sig, n)</code> goes back <code>n</code> cycles</li>
              </ul>
              <p>Open <code>stable_check.sv</code>. The spec is: <em>while <code>valid</code> is high and <code>ready</code> is low, <code>data</code> must not change on the next cycle.</em></p>
              <p>Complete the property body using <code>(valid && !ready) |=> $stable(data)</code>.</p>
              <blockquote><p><code>$stable(data)</code> is equivalent to writing <code>data == $past(data)</code> — use whichever reads more naturally for your spec.</p></blockquote>
            `,
            files: {
              a: {
                '/src/stable_check.sv': 'module stable_check(\n  input logic clk,\n  input logic valid, ready,\n  input logic [7:0] data\n);\n  property data_stable_p;\n    @(posedge clk)\n      // TODO: (valid && !ready) |=> $stable(data);\n      ;\n  endproperty\n\n  data_stable_a: assert property (data_stable_p);\n\nendmodule\n'
              },
              b: {
                '/src/stable_check.sv': 'module stable_check(\n  input logic clk,\n  input logic valid, ready,\n  input logic [7:0] data\n);\n  property data_stable_p;\n    @(posedge clk)\n      (valid && !ready) |=> $stable(data);\n  endproperty\n\n  data_stable_a: assert property (data_stable_p);\n\nendmodule\n'
              }
            }
          }
        ]
      },
      // ── Chapter 5: Coverage ───────────────────────────────────────────────
      {
        title: 'Coverage',
        lessons: [
          {
            slug: 'sva/cover-property',
            title: 'cover property',
            waveform: 'required',
            focus: '/src/bus_check.sv',
            html: `
              <p>If an assertion never fires, it could mean the design is correct — or that the triggering condition was <em>never exercised</em>. These are very different situations.</p>
              <p><code>cover property</code> resolves this ambiguity. Its pass action runs each time the property <em>succeeds</em>, confirming the antecedent was actually stimulated:</p>
              <pre>aP: assert property (p) else $display("FAIL");
cP: cover  property (p)      $display("PASS");</pre>
              <p>Open <code>bus_check.sv</code>. The property <code>ldpcheck</code> is already written. Add both the <code>assert property</code> and <code>cover property</code> statements.</p>
              <blockquote><p>Always pair <code>assert</code> and <code>cover</code> on the same property. A simulation that sees no assertion failures but also no cover hits has told you almost nothing.</p></blockquote>
            `,
            files: {
              a: {
                '/src/bus_check.sv': 'module bus_check(input logic clk, frame_, ldp_);\n\n  property ldpcheck;\n    @(posedge clk) $rose(frame_) |-> ##[1:2] $fell(ldp_);\n  endproperty\n\n  // TODO: aP: assert property (ldpcheck) else $display("ldpcheck FAIL");\n  // TODO: cP: cover  property (ldpcheck)      $display("ldpcheck PASS");\n\nendmodule\n'
              },
              b: {
                '/src/bus_check.sv': 'module bus_check(input logic clk, frame_, ldp_);\n\n  property ldpcheck;\n    @(posedge clk) $rose(frame_) |-> ##[1:2] $fell(ldp_);\n  endproperty\n\n  aP: assert property (ldpcheck)\n    else $display("ldpcheck FAIL");\n  cP: cover property (ldpcheck)\n    $display("ldpcheck PASS");\n\nendmodule\n'
              }
            }
          }
        ]
      },
      // ── Chapter 6: Advanced Properties ───────────────────────────────────
      {
        title: 'Advanced Properties',
        lessons: [
          {
            slug: 'sva/local-vars',
            title: 'Local Variables in Sequences',
            waveform: 'required',
            focus: '/src/pipeline_check.sv',
            html: `
              <p>A <strong>local variable</strong> in a sequence captures a signal's value at one clock edge and carries it forward to a later comparison — something you cannot do with plain signal references:</p>
              <pre>property pipe_p;
  int v;
  @(posedge clk)
    (valid_in, v = in_data) |=> ##2 (out_data == v);
endproperty</pre>
              <p>The comma operator <code>(cond, v = expr)</code> simultaneously checks the trigger condition and assigns to the local variable. The variable retains its value across the subsequent clock-delay cycles.</p>
              <p>Open <code>pipeline_check.sv</code>. Capture <code>in_data</code> when <code>valid_in</code> is high, then verify that <code>out_data</code> equals it exactly 3 cycles later.</p>
              <blockquote><p>Local variables are thread-local: every concurrent evaluation of the sequence gets its own copy, so overlapping in-flight transactions are checked independently.</p></blockquote>
            `,
            files: {
              a: {
                '/src/pipeline_check.sv': 'module pipeline_check(\n  input logic        clk,\n  input logic        valid_in,\n  input logic [7:0]  in_data,\n  input logic [7:0]  out_data\n);\n\n  property pipe_latency_p;\n    int v;\n    @(posedge clk)\n      // TODO: (valid_in, v = in_data) |=> ##2 (out_data == v);\n      ;\n  endproperty\n\n  pipe_latency_a: assert property (pipe_latency_p);\n\nendmodule\n'
              },
              b: {
                '/src/pipeline_check.sv': 'module pipeline_check(\n  input logic        clk,\n  input logic        valid_in,\n  input logic [7:0]  in_data,\n  input logic [7:0]  out_data\n);\n\n  property pipe_latency_p;\n    int v;\n    @(posedge clk)\n      (valid_in, v = in_data) |=> ##2 (out_data == v);\n  endproperty\n\n  pipe_latency_a: assert property (pipe_latency_p);\n\nendmodule\n'
              }
            }
          },
          {
            slug: 'sva/onehot',
            title: '$onehot, $onehot0, $countones',
            waveform: 'required',
            focus: '/src/arbiter_check.sv',
            html: `
              <p>SystemVerilog provides built-in functions for checking bit-count invariants — exactly what bus arbiters need:</p>
              <ul>
                <li><code>$onehot(v)</code> — true when <em>exactly one</em> bit of <code>v</code> is 1</li>
                <li><code>$onehot0(v)</code> — true when <em>zero or one</em> bits are 1</li>
                <li><code>$countones(v)</code> — returns the <em>number</em> of set bits; use in expressions like <code>$countones(v) &lt;= 2</code></li>
              </ul>
              <p>Open <code>arbiter_check.sv</code> and add two properties:</p>
              <ol>
                <li><strong>grant_onehot_p</strong>: whenever <code>any_grant</code> is high, <code>grant</code> must be one-hot — use <code>$onehot(grant)</code></li>
                <li><strong>grant_idle_p</strong>: whenever <code>any_grant</code> is low, <code>grant</code> must be all zeros</li>
              </ol>
              <blockquote><p><code>|req</code> is a reduction OR: it is 1 if any bit of <code>req</code> is 1. It is often used as a shorthand antecedent: <code>|req |-> $onehot0(gnt)</code> means "when any request is active, at most one grant is given."</p></blockquote>
            `,
            files: {
              a: {
                '/src/arbiter_check.sv': "module arbiter_check(\n  input logic       clk,\n  input logic [3:0] req,\n  input logic [3:0] grant,\n  input logic       any_grant\n);\n\n  // TODO: property grant_onehot_p:\n  //   @(posedge clk) any_grant |-> $onehot(grant);\n\n  // TODO: property grant_idle_p:\n  //   @(posedge clk) !any_grant |-> (grant == 4'b0);\n\n  // TODO: assert both properties\n\nendmodule\n"
              },
              b: {
                '/src/arbiter_check.sv': "module arbiter_check(\n  input logic       clk,\n  input logic [3:0] req,\n  input logic [3:0] grant,\n  input logic       any_grant\n);\n\n  property grant_onehot_p;\n    @(posedge clk) any_grant |-> $onehot(grant);\n  endproperty\n\n  property grant_idle_p;\n    @(posedge clk) !any_grant |-> (grant == 4'b0);\n  endproperty\n\n  grant_onehot_a: assert property (grant_onehot_p);\n  grant_idle_a:   assert property (grant_idle_p);\n\nendmodule\n"
              }
            }
          }
        ]
      }
    ]
  },

  // ─────────────────────────────────────────────────────────────────────────
  //  PART 3: Universal Verification Methodology (UVM)
  // ─────────────────────────────────────────────────────────────────────────
  {
    title: 'Universal Verification Methodology',
    chapters: [
      // ── Chapter 1: UVM Foundations ────────────────────────────────────────
      {
        title: 'UVM Foundations',
        lessons: [
          {
            slug: 'uvm/reporting',
            title: 'The First UVM Test',
            waveform: 'off',
            focus: '/src/my_test.sv',
            html: `
              <p>UVM provides four reporting macros that include automatic component-name and file/line information:</p>
              <ul>
                <li><code>\`uvm_info(ID, msg, verbosity)</code> — informational; gated by verbosity level</li>
                <li><code>\`uvm_warning(ID, msg)</code> — always printed; increments warning count</li>
                <li><code>\`uvm_error(ID, msg)</code> — always printed; increments error count; simulation continues</li>
                <li><code>\`uvm_fatal(ID, msg)</code> — always printed; immediately calls <code>$finish</code></li>
              </ul>
              <p>A UVM run starts with <code>run_test("test_name")</code> from the static top-level module. UVM constructs the named test class and drives it through a sequence of <strong>phases</strong>. The critical phase is <code>run_phase</code> — the only time-consuming one. Simulation does not advance past it until all components drop their <strong>objections</strong>:</p>
              <pre>task run_phase(uvm_phase phase);
  phase.raise_objection(this);  // hold simulation open
  // ... do work ...
  phase.drop_objection(this);   // allow simulation to end
endtask</pre>
              <p>Open <code>my_test.sv</code> and complete the <code>run_phase</code> body.</p>
              <blockquote><p>Forgetting to call <code>drop_objection</code> is the most common beginner UVM bug — simulation will run forever. Always pair raise with drop.</p></blockquote>
            `,
            files: {
              a: {
                '/src/my_test.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass my_test extends uvm_test;\n  `uvm_component_utils(my_test)\n\n  function new(string name, uvm_component parent);\n    super.new(name, parent);\n  endfunction\n\n  task run_phase(uvm_phase phase);\n    // TODO 1: phase.raise_objection(this);\n    // TODO 2: `uvm_info(\"TEST\", \"Hello from UVM!\", UVM_LOW)\n    // TODO 3: `uvm_error(\"TEST\", \"Intentional error — simulation continues\")\n    // TODO 4: phase.drop_objection(this);\n  endtask\nendclass\n",
                '/src/tb_top.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n`include \"my_test.sv\"\n\nmodule tb_top;\n  initial run_test(\"my_test\");\nendmodule\n"
              },
              b: {
                '/src/my_test.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass my_test extends uvm_test;\n  `uvm_component_utils(my_test)\n\n  function new(string name, uvm_component parent);\n    super.new(name, parent);\n  endfunction\n\n  task run_phase(uvm_phase phase);\n    phase.raise_objection(this);\n    `uvm_info(\"TEST\", \"Hello from UVM!\", UVM_LOW)\n    `uvm_error(\"TEST\", \"Intentional error — simulation continues\")\n    phase.drop_objection(this);\n  endtask\nendclass\n"
              }
            }
          },
          {
            slug: 'uvm/seq-item',
            title: 'Sequence Items',
            waveform: 'off',
            focus: '/src/adder_item.sv',
            html: `
              <p>A <strong>sequence item</strong> is the transaction data object that flows through a UVM testbench. It extends <code>uvm_sequence_item</code> and holds the stimulus fields.</p>
              <p>Fields marked <code>rand</code> are randomizable. <strong>Constraints</strong> narrow the random space to legal values. The <strong>factory registration macro</strong> enables type overrides and auto-generates <code>print()</code>, <code>copy()</code>, and <code>compare()</code>:</p>
              <pre>class adder_item extends uvm_sequence_item;
  \`uvm_object_utils_begin(adder_item)
    \`uvm_field_int(a, UVM_ALL_ON)
    \`uvm_field_int(b, UVM_ALL_ON)
  \`uvm_object_utils_end

  rand logic [7:0] a, b;
  constraint small_c { a &lt; 100; b &lt; 100; }
  ...
endclass</pre>
              <p>Open <code>adder_item.sv</code> and add the <code>rand</code> declarations, field macros, and constraint.</p>
              <blockquote><p>Always create items through the factory: <code>adder_item::type_id::create("item")</code> — not with <code>new</code> directly. Factory creation enables test-level type substitution without changing any sequence code.</p></blockquote>
            `,
            files: {
              a: {
                '/src/adder_item.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_item extends uvm_sequence_item;\n  `uvm_object_utils_begin(adder_item)\n    // TODO: `uvm_field_int(a, UVM_ALL_ON)\n    // TODO: `uvm_field_int(b, UVM_ALL_ON)\n  `uvm_object_utils_end\n\n  // TODO: rand logic [7:0] a, b;\n\n  // TODO: constraint small_c { a < 100; b < 100; }\n\n  function new(string name = \"adder_item\");\n    super.new(name);\n  endfunction\n\n  function string convert2string();\n    return $sformatf(\"a=%3d b=%3d\", a, b);\n  endfunction\nendclass\n",
                '/src/tb_top.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n`include \"adder_item.sv\"\n\nmodule tb_top;\n  initial begin\n    adder_item item;\n    repeat (5) begin\n      item = adder_item::type_id::create(\"item\");\n      void'(item.randomize());\n      $display(\"%s  expected_sum=%0d\", item.convert2string(), item.a + item.b);\n    end\n  end\nendmodule\n"
              },
              b: {
                '/src/adder_item.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_item extends uvm_sequence_item;\n  `uvm_object_utils_begin(adder_item)\n    `uvm_field_int(a, UVM_ALL_ON)\n    `uvm_field_int(b, UVM_ALL_ON)\n  `uvm_object_utils_end\n\n  rand logic [7:0] a, b;\n\n  constraint small_c { a < 100; b < 100; }\n\n  function new(string name = \"adder_item\");\n    super.new(name);\n  endfunction\n\n  function string convert2string();\n    return $sformatf(\"a=%3d b=%3d\", a, b);\n  endfunction\nendclass\n"
              }
            }
          }
        ]
      },
      // ── Chapter 2: Stimulus ───────────────────────────────────────────────
      {
        title: 'Stimulus',
        lessons: [
          {
            slug: 'uvm/sequence',
            title: 'Sequences',
            waveform: 'off',
            focus: '/src/adder_seq.sv',
            html: `
              <p>A <strong>sequence</strong> generates a stream of transactions. Its <code>body()</code> task runs when the sequence is started on a sequencer. The three-step handshake with the driver is:</p>
              <ol>
                <li><code>start_item(item)</code> — request access; blocks until the sequencer grants it</li>
                <li>Randomize or configure the item while holding the grant</li>
                <li><code>finish_item(item)</code> — hand the item to the driver; blocks until the driver calls <code>item_done()</code></li>
              </ol>
              <p>Open <code>adder_seq.sv</code> and complete the <code>body()</code> task. The driver and agent are already provided — focus on the sequence side of the handshake.</p>
              <blockquote><p>Sequences are objects (<code>uvm_object</code>), not components — they have no phases. Start them explicitly from a test's <code>run_phase</code> with <code>seq.start(sequencer_handle)</code>.</p></blockquote>
            `,
            files: {
              a: {
                '/src/adder_item.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_item extends uvm_sequence_item;\n  `uvm_object_utils_begin(adder_item)\n    `uvm_field_int(a, UVM_ALL_ON)\n    `uvm_field_int(b, UVM_ALL_ON)\n  `uvm_object_utils_end\n  rand logic [7:0] a, b;\n  constraint small_c { a < 100; b < 100; }\n  function new(string name = \"adder_item\"); super.new(name); endfunction\n  function string convert2string();\n    return $sformatf(\"a=%3d b=%3d\", a, b);\n  endfunction\nendclass\n",
                '/src/adder_seq.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_seq extends uvm_sequence #(adder_item);\n  `uvm_object_utils(adder_seq)\n  int unsigned num_items = 5;\n  function new(string name = \"adder_seq\"); super.new(name); endfunction\n  task body();\n    repeat (num_items) begin\n      adder_item item = adder_item::type_id::create(\"item\");\n      // TODO: start_item(item);\n      // TODO: void'(item.randomize());\n      // TODO: `uvm_info(\"SEQ\", item.convert2string(), UVM_MEDIUM)\n      // TODO: finish_item(item);\n    end\n  endtask\nendclass\n",
                '/src/adder_driver.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\n// Stub driver — acknowledges items without a real DUT\nclass adder_driver extends uvm_driver #(adder_item);\n  `uvm_component_utils(adder_driver)\n  function new(string name, uvm_component parent); super.new(name, parent); endfunction\n  task run_phase(uvm_phase phase);\n    adder_item req;\n    forever begin\n      seq_item_port.get_next_item(req);\n      #10;\n      seq_item_port.item_done();\n    end\n  endtask\nendclass\n",
                '/src/adder_agent.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_agent extends uvm_agent;\n  `uvm_component_utils(adder_agent)\n  adder_driver drv;\n  uvm_sequencer #(adder_item) seqr;\n  function new(string name, uvm_component parent); super.new(name, parent); endfunction\n  function void build_phase(uvm_phase phase);\n    super.build_phase(phase);\n    seqr = uvm_sequencer #(adder_item)::type_id::create(\"seqr\", this);\n    drv  = adder_driver::type_id::create(\"drv\", this);\n  endfunction\n  function void connect_phase(uvm_phase phase);\n    drv.seq_item_port.connect(seqr.seq_item_export);\n  endfunction\nendclass\n",
                '/src/tb_top.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n`include \"adder_item.sv\"\n`include \"adder_driver.sv\"\n`include \"adder_agent.sv\"\n`include \"adder_seq.sv\"\n\nclass seq_test extends uvm_test;\n  `uvm_component_utils(seq_test)\n  adder_agent agent;\n  function new(string name, uvm_component parent); super.new(name, parent); endfunction\n  function void build_phase(uvm_phase phase);\n    super.build_phase(phase);\n    agent = adder_agent::type_id::create(\"agent\", this);\n  endfunction\n  task run_phase(uvm_phase phase);\n    adder_seq seq = adder_seq::type_id::create(\"seq\");\n    phase.raise_objection(this);\n    seq.start(agent.seqr);\n    phase.drop_objection(this);\n  endtask\nendclass\n\nmodule tb_top;\n  initial run_test(\"seq_test\");\nendmodule\n"
              },
              b: {
                '/src/adder_seq.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_seq extends uvm_sequence #(adder_item);\n  `uvm_object_utils(adder_seq)\n  int unsigned num_items = 5;\n  function new(string name = \"adder_seq\"); super.new(name); endfunction\n  task body();\n    repeat (num_items) begin\n      adder_item item = adder_item::type_id::create(\"item\");\n      start_item(item);\n      void'(item.randomize());\n      `uvm_info(\"SEQ\", item.convert2string(), UVM_MEDIUM)\n      finish_item(item);\n    end\n  endtask\nendclass\n"
              }
            }
          },
          {
            slug: 'uvm/driver',
            title: 'The Driver',
            waveform: 'optional',
            focus: '/src/adder_driver.sv',
            html: `
              <p>The <strong>driver</strong> is where the UVM world meets RTL. It pulls transactions from the sequencer, converts them to pin-level stimulus, and signals completion:</p>
              <pre>task run_phase(uvm_phase phase);
  adder_item req;
  forever begin
    seq_item_port.get_next_item(req);  // pull; blocks if empty
    @(posedge vif.clk);
    vif.a &lt;= req.a;
    vif.b &lt;= req.b;
    @(posedge vif.clk);
    seq_item_port.item_done();         // unblocks finish_item
  end
endtask</pre>
              <p>The DUT is accessed through a <strong>virtual interface</strong> handle retrieved from <code>uvm_config_db</code> in <code>build_phase</code>:</p>
              <pre>if (!uvm_config_db #(virtual adder_if)::get(this, "", "vif", vif))
  \`uvm_fatal("NOVIF", "Virtual interface not found")</pre>
              <p>Open <code>adder_driver.sv</code> and complete <code>build_phase</code> (config_db get) and <code>run_phase</code> (drive the interface).</p>
              <blockquote><p>The virtual interface is the only bridge from the dynamic class world into the static module world. It must be <code>set</code> in <code>tb_top</code> before <code>run_test()</code> is called, and <code>get</code> by every component that needs DUT access.</p></blockquote>
            `,
            files: {
              a: {
                '/src/adder.sv': "module adder (\n  input  logic [7:0] a, b,\n  output logic [7:0] sum,\n  output logic       carry\n);\n  assign {carry, sum} = a + b;\nendmodule\n",
                '/src/adder_if.sv': "interface adder_if (input logic clk);\n  logic [7:0] a, b, sum;\n  logic       carry;\nendinterface\n",
                '/src/adder_item.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_item extends uvm_sequence_item;\n  `uvm_object_utils_begin(adder_item)\n    `uvm_field_int(a, UVM_ALL_ON)\n    `uvm_field_int(b, UVM_ALL_ON)\n  `uvm_object_utils_end\n  rand logic [7:0] a, b;\n  constraint small_c { a < 100; b < 100; }\n  function new(string name = \"adder_item\"); super.new(name); endfunction\n  function string convert2string();\n    return $sformatf(\"a=%3d b=%3d\", a, b);\n  endfunction\nendclass\n",
                '/src/adder_seq.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_seq extends uvm_sequence #(adder_item);\n  `uvm_object_utils(adder_seq)\n  int unsigned num_items = 5;\n  function new(string name = \"adder_seq\"); super.new(name); endfunction\n  task body();\n    repeat (num_items) begin\n      adder_item item = adder_item::type_id::create(\"item\");\n      start_item(item);\n      void'(item.randomize());\n      `uvm_info(\"SEQ\", item.convert2string(), UVM_MEDIUM)\n      finish_item(item);\n    end\n  endtask\nendclass\n",
                '/src/adder_driver.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_driver extends uvm_driver #(adder_item);\n  `uvm_component_utils(adder_driver)\n  virtual adder_if vif;\n  function new(string name, uvm_component parent);\n    super.new(name, parent);\n  endfunction\n  function void build_phase(uvm_phase phase);\n    super.build_phase(phase);\n    // TODO: retrieve vif from config_db:\n    // if (!uvm_config_db #(virtual adder_if)::get(this, \"\", \"vif\", vif))\n    //   `uvm_fatal(\"NOVIF\", \"Virtual interface not found\")\n  endfunction\n  task run_phase(uvm_phase phase);\n    adder_item req;\n    forever begin\n      seq_item_port.get_next_item(req);\n      // TODO: @(posedge vif.clk);\n      // TODO: vif.a <= req.a;\n      // TODO: vif.b <= req.b;\n      // TODO: @(posedge vif.clk);\n      seq_item_port.item_done();\n    end\n  endtask\nendclass\n",
                '/src/adder_agent.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_agent extends uvm_agent;\n  `uvm_component_utils(adder_agent)\n  adder_driver drv;\n  uvm_sequencer #(adder_item) seqr;\n  function new(string name, uvm_component parent); super.new(name, parent); endfunction\n  function void build_phase(uvm_phase phase);\n    super.build_phase(phase);\n    seqr = uvm_sequencer #(adder_item)::type_id::create(\"seqr\", this);\n    drv  = adder_driver::type_id::create(\"drv\", this);\n  endfunction\n  function void connect_phase(uvm_phase phase);\n    drv.seq_item_port.connect(seqr.seq_item_export);\n  endfunction\nendclass\n",
                '/src/tb_top.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n`include \"adder_item.sv\"\n`include \"adder_driver.sv\"\n`include \"adder_agent.sv\"\n`include \"adder_seq.sv\"\n\nclass driver_test extends uvm_test;\n  `uvm_component_utils(driver_test)\n  adder_agent agent;\n  function new(string name, uvm_component parent); super.new(name, parent); endfunction\n  function void build_phase(uvm_phase phase);\n    super.build_phase(phase);\n    agent = adder_agent::type_id::create(\"agent\", this);\n  endfunction\n  task run_phase(uvm_phase phase);\n    adder_seq seq = adder_seq::type_id::create(\"seq\");\n    phase.raise_objection(this);\n    seq.start(agent.seqr);\n    phase.drop_objection(this);\n  endtask\nendclass\n\nmodule tb_top;\n  import uvm_pkg::*;\n  `include \"uvm_macros.svh\"\n  logic clk = 0;\n  always #5 clk = ~clk;\n  adder_if aif(.clk(clk));\n  adder dut(.a(aif.a), .b(aif.b), .sum(aif.sum), .carry(aif.carry));\n  initial begin\n    uvm_config_db #(virtual adder_if)::set(null, \"uvm_test_top.*\", \"vif\", aif);\n    run_test(\"driver_test\");\n  end\nendmodule\n"
              },
              b: {
                '/src/adder_driver.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_driver extends uvm_driver #(adder_item);\n  `uvm_component_utils(adder_driver)\n  virtual adder_if vif;\n  function new(string name, uvm_component parent);\n    super.new(name, parent);\n  endfunction\n  function void build_phase(uvm_phase phase);\n    super.build_phase(phase);\n    if (!uvm_config_db #(virtual adder_if)::get(this, \"\", \"vif\", vif))\n      `uvm_fatal(\"NOVIF\", \"Virtual interface not found\")\n  endfunction\n  task run_phase(uvm_phase phase);\n    adder_item req;\n    forever begin\n      seq_item_port.get_next_item(req);\n      @(posedge vif.clk);\n      vif.a <= req.a;\n      vif.b <= req.b;\n      @(posedge vif.clk);\n      seq_item_port.item_done();\n    end\n  endtask\nendclass\n"
              }
            }
          }
        ]
      },
      // ── Chapter 3: Checking ───────────────────────────────────────────────
      {
        title: 'Checking',
        lessons: [
          {
            slug: 'uvm/monitor',
            title: 'Monitor and Scoreboard',
            waveform: 'optional',
            focus: '/src/adder_scoreboard.sv',
            html: `
              <p>The <strong>monitor</strong> passively observes DUT signals and broadcasts completed transactions via a <code>uvm_analysis_port</code>. It does not drive anything.</p>
              <p>The <strong>scoreboard</strong> subscribes using a <code>uvm_analysis_imp</code> and a <code>write()</code> method. Every time the monitor broadcasts, <code>write()</code> is called automatically:</p>
              <pre>// In the scoreboard:
uvm_analysis_imp #(adder_item, adder_scoreboard) analysis_export;
...
function void write(adder_item item);
  logic [8:0] expected = 9'(item.a) + 9'(item.b);
  if (item.sum === expected[7:0] && item.carry === expected[8])
    pass_count++;
  else
    \`uvm_error("SCBD", "Mismatch!")
endfunction</pre>
              <p>Open <code>adder_scoreboard.sv</code> and complete the <code>write()</code> function.</p>
              <blockquote><p>The analysis port is one-to-many: the monitor does not know how many subscribers are connected. Attach a coverage collector alongside the scoreboard by connecting both to the same <code>ap</code> — the monitor code does not change.</p></blockquote>
            `,
            files: {
              a: {
                '/src/adder.sv': "module adder (\n  input  logic [7:0] a, b,\n  output logic [7:0] sum,\n  output logic       carry\n);\n  assign {carry, sum} = a + b;\nendmodule\n",
                '/src/adder_if.sv': "interface adder_if (input logic clk);\n  logic [7:0] a, b, sum;\n  logic       carry;\nendinterface\n",
                '/src/adder_item.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_item extends uvm_sequence_item;\n  `uvm_object_utils_begin(adder_item)\n    `uvm_field_int(a,     UVM_ALL_ON)\n    `uvm_field_int(b,     UVM_ALL_ON)\n    `uvm_field_int(sum,   UVM_ALL_ON)\n    `uvm_field_int(carry, UVM_ALL_ON)\n  `uvm_object_utils_end\n  rand logic [7:0] a, b;\n  logic [7:0] sum;\n  logic       carry;\n  constraint small_c { a < 100; b < 100; }\n  function new(string name = \"adder_item\"); super.new(name); endfunction\n  function string convert2string();\n    return $sformatf(\"a=%3d b=%3d => sum=%3d carry=%b\", a, b, sum, carry);\n  endfunction\nendclass\n",
                '/src/adder_seq.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_seq extends uvm_sequence #(adder_item);\n  `uvm_object_utils(adder_seq)\n  int unsigned num_items = 8;\n  function new(string name = \"adder_seq\"); super.new(name); endfunction\n  task body();\n    repeat (num_items) begin\n      adder_item item = adder_item::type_id::create(\"item\");\n      start_item(item); void'(item.randomize()); finish_item(item);\n    end\n  endtask\nendclass\n",
                '/src/adder_driver.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_driver extends uvm_driver #(adder_item);\n  `uvm_component_utils(adder_driver)\n  virtual adder_if vif;\n  function new(string name, uvm_component parent); super.new(name, parent); endfunction\n  function void build_phase(uvm_phase phase);\n    super.build_phase(phase);\n    if (!uvm_config_db #(virtual adder_if)::get(this, \"\", \"vif\", vif))\n      `uvm_fatal(\"NOVIF\", \"Virtual interface not found\")\n  endfunction\n  task run_phase(uvm_phase phase);\n    adder_item req;\n    forever begin\n      seq_item_port.get_next_item(req);\n      @(posedge vif.clk); vif.a <= req.a; vif.b <= req.b;\n      @(posedge vif.clk); seq_item_port.item_done();\n    end\n  endtask\nendclass\n",
                '/src/adder_monitor.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_monitor extends uvm_monitor;\n  `uvm_component_utils(adder_monitor)\n  virtual adder_if vif;\n  uvm_analysis_port #(adder_item) ap;\n  function new(string name, uvm_component parent); super.new(name, parent); endfunction\n  function void build_phase(uvm_phase phase);\n    super.build_phase(phase);\n    ap = new(\"ap\", this);\n    if (!uvm_config_db #(virtual adder_if)::get(this, \"\", \"vif\", vif))\n      `uvm_fatal(\"NOVIF\", \"Virtual interface not found\")\n  endfunction\n  task run_phase(uvm_phase phase);\n    adder_item item;\n    @(posedge vif.clk);\n    forever begin\n      @(posedge vif.clk);\n      item = adder_item::type_id::create(\"item\");\n      item.a = vif.a; item.b = vif.b;\n      item.sum = vif.sum; item.carry = vif.carry;\n      ap.write(item);\n    end\n  endtask\nendclass\n",
                '/src/adder_scoreboard.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_scoreboard extends uvm_scoreboard;\n  `uvm_component_utils(adder_scoreboard)\n  uvm_analysis_imp #(adder_item, adder_scoreboard) analysis_export;\n  int pass_count, fail_count;\n  function new(string name, uvm_component parent); super.new(name, parent); endfunction\n  function void build_phase(uvm_phase phase);\n    super.build_phase(phase);\n    analysis_export = new(\"analysis_export\", this);\n  endfunction\n  function void write(adder_item item);\n    logic [8:0] expected = 9'(item.a) + 9'(item.b);\n    // TODO: if actual matches expected, `uvm_info PASS, pass_count++\n    //       else `uvm_error FAIL, fail_count++\n  endfunction\n  function void report_phase(uvm_phase phase);\n    `uvm_info(\"SCBD\", $sformatf(\"Results: PASS=%0d FAIL=%0d\", pass_count, fail_count), UVM_LOW)\n  endfunction\nendclass\n",
                '/src/adder_agent.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_agent extends uvm_agent;\n  `uvm_component_utils(adder_agent)\n  adder_driver  drv;\n  adder_monitor mon;\n  uvm_sequencer #(adder_item) seqr;\n  function new(string name, uvm_component parent); super.new(name, parent); endfunction\n  function void build_phase(uvm_phase phase);\n    super.build_phase(phase);\n    seqr = uvm_sequencer #(adder_item)::type_id::create(\"seqr\", this);\n    drv  = adder_driver::type_id::create(\"drv\", this);\n    mon  = adder_monitor::type_id::create(\"mon\", this);\n  endfunction\n  function void connect_phase(uvm_phase phase);\n    drv.seq_item_port.connect(seqr.seq_item_export);\n  endfunction\nendclass\n",
                '/src/tb_top.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n`include \"adder_item.sv\"\n`include \"adder_driver.sv\"\n`include \"adder_monitor.sv\"\n`include \"adder_scoreboard.sv\"\n`include \"adder_agent.sv\"\n`include \"adder_seq.sv\"\n\nclass monitor_test extends uvm_test;\n  `uvm_component_utils(monitor_test)\n  adder_agent      agent;\n  adder_scoreboard scbd;\n  function new(string name, uvm_component parent); super.new(name, parent); endfunction\n  function void build_phase(uvm_phase phase);\n    super.build_phase(phase);\n    agent = adder_agent::type_id::create(\"agent\", this);\n    scbd  = adder_scoreboard::type_id::create(\"scbd\", this);\n  endfunction\n  function void connect_phase(uvm_phase phase);\n    agent.mon.ap.connect(scbd.analysis_export);\n  endfunction\n  task run_phase(uvm_phase phase);\n    adder_seq seq = adder_seq::type_id::create(\"seq\");\n    phase.raise_objection(this);\n    seq.start(agent.seqr);\n    phase.drop_objection(this);\n  endtask\nendclass\n\nmodule tb_top;\n  import uvm_pkg::*;\n  `include \"uvm_macros.svh\"\n  logic clk = 0;\n  always #5 clk = ~clk;\n  adder_if aif(.clk(clk));\n  adder dut(.a(aif.a), .b(aif.b), .sum(aif.sum), .carry(aif.carry));\n  initial begin\n    uvm_config_db #(virtual adder_if)::set(null, \"uvm_test_top.*\", \"vif\", aif);\n    run_test(\"monitor_test\");\n  end\nendmodule\n"
              },
              b: {
                '/src/adder_scoreboard.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_scoreboard extends uvm_scoreboard;\n  `uvm_component_utils(adder_scoreboard)\n  uvm_analysis_imp #(adder_item, adder_scoreboard) analysis_export;\n  int pass_count, fail_count;\n  function new(string name, uvm_component parent); super.new(name, parent); endfunction\n  function void build_phase(uvm_phase phase);\n    super.build_phase(phase);\n    analysis_export = new(\"analysis_export\", this);\n  endfunction\n  function void write(adder_item item);\n    logic [8:0] expected = 9'(item.a) + 9'(item.b);\n    if (item.sum === expected[7:0] && item.carry === expected[8]) begin\n      pass_count++;\n      `uvm_info(\"SCBD\", {\"PASS: \", item.convert2string()}, UVM_MEDIUM)\n    end else begin\n      fail_count++;\n      `uvm_error(\"SCBD\", $sformatf(\"FAIL: %s -- expected sum=%0d carry=%b\",\n        item.convert2string(), expected[7:0], expected[8]))\n    end\n  endfunction\n  function void report_phase(uvm_phase phase);\n    `uvm_info(\"SCBD\", $sformatf(\"Results: PASS=%0d FAIL=%0d\", pass_count, fail_count), UVM_LOW)\n  endfunction\nendclass\n"
              }
            }
          },
          {
            slug: 'uvm/env',
            title: 'Environment and Test',
            waveform: 'optional',
            focus: '/src/adder_env.sv',
            html: `
              <p>The <strong>environment</strong> (<code>uvm_env</code>) is the container that assembles agents and scoreboards. Its two key phases:</p>
              <ul>
                <li><code>build_phase</code> — creates child components top-down with <code>type_id::create("name", this)</code></li>
                <li><code>connect_phase</code> — wires TLM ports between components bottom-up</li>
              </ul>
              <pre>function void build_phase(uvm_phase phase);
  super.build_phase(phase);
  agent = adder_agent::type_id::create("agent", this);
  scbd  = adder_scoreboard::type_id::create("scbd",  this);
endfunction

function void connect_phase(uvm_phase phase);
  agent.mon.ap.connect(scbd.analysis_export);
endfunction</pre>
              <p>Open <code>adder_env.sv</code> and complete both phases. All other components are provided — this is the final piece that makes the full testbench run end-to-end.</p>
              <blockquote><p>The <code>this</code> argument in <code>create("name", this)</code> sets the UVM hierarchy parent. This determines the component's path in the tree, which scopes config_db lookups and reporting output.</p></blockquote>
            `,
            files: {
              a: {
                '/src/adder.sv': "module adder (\n  input  logic [7:0] a, b,\n  output logic [7:0] sum,\n  output logic       carry\n);\n  assign {carry, sum} = a + b;\nendmodule\n",
                '/src/adder_if.sv': "interface adder_if (input logic clk);\n  logic [7:0] a, b, sum;\n  logic       carry;\nendinterface\n",
                '/src/adder_item.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_item extends uvm_sequence_item;\n  `uvm_object_utils_begin(adder_item)\n    `uvm_field_int(a,     UVM_ALL_ON)\n    `uvm_field_int(b,     UVM_ALL_ON)\n    `uvm_field_int(sum,   UVM_ALL_ON)\n    `uvm_field_int(carry, UVM_ALL_ON)\n  `uvm_object_utils_end\n  rand logic [7:0] a, b;\n  logic [7:0] sum;\n  logic       carry;\n  constraint small_c { a < 100; b < 100; }\n  function new(string name = \"adder_item\"); super.new(name); endfunction\n  function string convert2string();\n    return $sformatf(\"a=%3d b=%3d => sum=%3d carry=%b\", a, b, sum, carry);\n  endfunction\nendclass\n",
                '/src/adder_seq.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_seq extends uvm_sequence #(adder_item);\n  `uvm_object_utils(adder_seq)\n  int unsigned num_items = 8;\n  function new(string name = \"adder_seq\"); super.new(name); endfunction\n  task body();\n    repeat (num_items) begin\n      adder_item item = adder_item::type_id::create(\"item\");\n      start_item(item); void'(item.randomize()); finish_item(item);\n    end\n  endtask\nendclass\n",
                '/src/adder_driver.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_driver extends uvm_driver #(adder_item);\n  `uvm_component_utils(adder_driver)\n  virtual adder_if vif;\n  function new(string name, uvm_component parent); super.new(name, parent); endfunction\n  function void build_phase(uvm_phase phase);\n    super.build_phase(phase);\n    if (!uvm_config_db #(virtual adder_if)::get(this, \"\", \"vif\", vif))\n      `uvm_fatal(\"NOVIF\", \"Virtual interface not found\")\n  endfunction\n  task run_phase(uvm_phase phase);\n    adder_item req;\n    forever begin\n      seq_item_port.get_next_item(req);\n      @(posedge vif.clk); vif.a <= req.a; vif.b <= req.b;\n      @(posedge vif.clk); seq_item_port.item_done();\n    end\n  endtask\nendclass\n",
                '/src/adder_monitor.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_monitor extends uvm_monitor;\n  `uvm_component_utils(adder_monitor)\n  virtual adder_if vif;\n  uvm_analysis_port #(adder_item) ap;\n  function new(string name, uvm_component parent); super.new(name, parent); endfunction\n  function void build_phase(uvm_phase phase);\n    super.build_phase(phase);\n    ap = new(\"ap\", this);\n    if (!uvm_config_db #(virtual adder_if)::get(this, \"\", \"vif\", vif))\n      `uvm_fatal(\"NOVIF\", \"Virtual interface not found\")\n  endfunction\n  task run_phase(uvm_phase phase);\n    adder_item item;\n    @(posedge vif.clk);\n    forever begin\n      @(posedge vif.clk);\n      item = adder_item::type_id::create(\"item\");\n      item.a = vif.a; item.b = vif.b;\n      item.sum = vif.sum; item.carry = vif.carry;\n      ap.write(item);\n    end\n  endtask\nendclass\n",
                '/src/adder_scoreboard.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_scoreboard extends uvm_scoreboard;\n  `uvm_component_utils(adder_scoreboard)\n  uvm_analysis_imp #(adder_item, adder_scoreboard) analysis_export;\n  int pass_count, fail_count;\n  function new(string name, uvm_component parent); super.new(name, parent); endfunction\n  function void build_phase(uvm_phase phase);\n    super.build_phase(phase);\n    analysis_export = new(\"analysis_export\", this);\n  endfunction\n  function void write(adder_item item);\n    logic [8:0] expected = 9'(item.a) + 9'(item.b);\n    if (item.sum === expected[7:0] && item.carry === expected[8]) begin\n      pass_count++;\n      `uvm_info(\"SCBD\", {\"PASS: \", item.convert2string()}, UVM_MEDIUM)\n    end else begin\n      fail_count++;\n      `uvm_error(\"SCBD\", $sformatf(\"FAIL: %s -- expected sum=%0d carry=%b\",\n        item.convert2string(), expected[7:0], expected[8]))\n    end\n  endfunction\n  function void report_phase(uvm_phase phase);\n    `uvm_info(\"SCBD\", $sformatf(\"Results: PASS=%0d FAIL=%0d\", pass_count, fail_count), UVM_LOW)\n  endfunction\nendclass\n",
                '/src/adder_agent.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_agent extends uvm_agent;\n  `uvm_component_utils(adder_agent)\n  adder_driver  drv;\n  adder_monitor mon;\n  uvm_sequencer #(adder_item) seqr;\n  function new(string name, uvm_component parent); super.new(name, parent); endfunction\n  function void build_phase(uvm_phase phase);\n    super.build_phase(phase);\n    seqr = uvm_sequencer #(adder_item)::type_id::create(\"seqr\", this);\n    drv  = adder_driver::type_id::create(\"drv\", this);\n    mon  = adder_monitor::type_id::create(\"mon\", this);\n  endfunction\n  function void connect_phase(uvm_phase phase);\n    drv.seq_item_port.connect(seqr.seq_item_export);\n  endfunction\nendclass\n",
                '/src/adder_env.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_env extends uvm_env;\n  `uvm_component_utils(adder_env)\n  adder_agent      agent;\n  adder_scoreboard scbd;\n  function new(string name, uvm_component parent); super.new(name, parent); endfunction\n  function void build_phase(uvm_phase phase);\n    super.build_phase(phase);\n    // TODO: agent = adder_agent::type_id::create(\"agent\", this);\n    // TODO: scbd  = adder_scoreboard::type_id::create(\"scbd\",  this);\n  endfunction\n  function void connect_phase(uvm_phase phase);\n    // TODO: agent.mon.ap.connect(scbd.analysis_export);\n  endfunction\nendclass\n",
                '/src/adder_test.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_test extends uvm_test;\n  `uvm_component_utils(adder_test)\n  adder_env env;\n  function new(string name, uvm_component parent); super.new(name, parent); endfunction\n  function void build_phase(uvm_phase phase);\n    super.build_phase(phase);\n    env = adder_env::type_id::create(\"env\", this);\n  endfunction\n  task run_phase(uvm_phase phase);\n    adder_seq seq = adder_seq::type_id::create(\"seq\");\n    phase.raise_objection(this);\n    seq.start(env.agent.seqr);\n    phase.drop_objection(this);\n  endtask\nendclass\n",
                '/src/tb_top.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n`include \"adder_item.sv\"\n`include \"adder_driver.sv\"\n`include \"adder_monitor.sv\"\n`include \"adder_scoreboard.sv\"\n`include \"adder_agent.sv\"\n`include \"adder_seq.sv\"\n`include \"adder_env.sv\"\n`include \"adder_test.sv\"\n\nmodule tb_top;\n  import uvm_pkg::*;\n  `include \"uvm_macros.svh\"\n  logic clk = 0;\n  always #5 clk = ~clk;\n  adder_if aif(.clk(clk));\n  adder dut(.a(aif.a), .b(aif.b), .sum(aif.sum), .carry(aif.carry));\n  initial begin\n    uvm_config_db #(virtual adder_if)::set(null, \"uvm_test_top.*\", \"vif\", aif);\n    run_test(\"adder_test\");\n  end\nendmodule\n"
              },
              b: {
                '/src/adder_env.sv': "import uvm_pkg::*;\n`include \"uvm_macros.svh\"\n\nclass adder_env extends uvm_env;\n  `uvm_component_utils(adder_env)\n  adder_agent      agent;\n  adder_scoreboard scbd;\n  function new(string name, uvm_component parent); super.new(name, parent); endfunction\n  function void build_phase(uvm_phase phase);\n    super.build_phase(phase);\n    agent = adder_agent::type_id::create(\"agent\", this);\n    scbd  = adder_scoreboard::type_id::create(\"scbd\",  this);\n  endfunction\n  function void connect_phase(uvm_phase phase);\n    agent.mon.ap.connect(scbd.analysis_export);\n  endfunction\nendclass\n"
              }
            }
          }
        ]
      }
    ]
  }
];

export { parts };

export const lessons = parts.flatMap((part) =>
  part.chapters.flatMap((chapter) =>
    chapter.lessons.map((lesson) => ({
      ...lesson,
      partTitle: part.title,
      chapterTitle: chapter.title
    }))
  )
);
