# Curriculum Tracker

Status of every lesson and a roadmap of what still needs to be written.
Lessons are keyed by slug (matches `tutorial-data.js`). Reference material
from https://github.com/karimmahmoud22/SystemVerilog-For-Verification is
noted where it is directly usable as a basis for a lesson.

Legend: ✅ exists · 📝 planned (prioritised) · 💡 optional/stretch

---

## Part 1 — SystemVerilog Basics

### Chapter: Introduction
| Slug | Title | Status |
|---|---|---|
| `sv/welcome` | Welcome | ✅ |
| `sv/modules-and-ports` | Modules and Ports | ✅ |

### Chapter: Combinational Logic
| Slug | Title | Status |
|---|---|---|
| `sv/always-comb` | always_comb and case | ✅ |
| `sv/priority-enc` | Priority Encoder (casez) | ✅ |
| `sv/assign-operators` | Operators & Arithmetic | 📝 |

> Cover reduction operators (`|req`), ternary, signed arithmetic,
> overflow — sets up concepts used in SVA and UVM lessons.
> Ref: `TipsAndTricks/ExpressionWidth.sv`, `TipsAndTricks/Casting.sv`

### Chapter: Sequential Logic
| Slug | Title | Status |
|---|---|---|
| `sv/always-ff` | Flip-Flops with always_ff | ✅ |
| `sv/counter` | Up-Counter | ✅ |
| `sv/shift-reg` | Shift Register | 📝 |

> Introduces `[*]` bus shift and multi-bit `always_ff`; prerequisite
> for pipeline assertions in Part 2.

### Chapter: Parameterized Modules
| Slug | Title | Status |
|---|---|---|
| `sv/parameters` | Parameters and localparam | ✅ |
| `sv/generate` | generate for / if | 📝 |

> `for generate` to replicate instances; used in every real chip.
> A parameterised N-bit adder array is a natural exercise.

### Chapter: Data Types
| Slug | Title | Status |
|---|---|---|
| `sv/packed-structs` | Packed Structs and Unions | 📝 |
| `sv/typedef` | typedef and type aliases | 📝 |
| `sv/arrays-static` | Static Arrays (packed & unpacked) | 📝 |

> Structs are pervasive in RTL (AXI, APB). Packed arrays underpin
> multi-bit signals. Ref: `DataTypes/DataTypes.sv`,
> `Arrays/PackedArrays.sv`, `Arrays/Packed_UnpackedArrays.sv`

### Chapter: Interfaces
| Slug | Title | Status |
|---|---|---|
| `sv/interfaces` | Interfaces and modport | 📝 |
| `sv/clocking-blocks` | Clocking Blocks | 💡 |

> **Critical gap.** `adder_if` is used fully-formed in all UVM lessons
> without ever being taught. Must come before Part 3.
> Ref: `ConnectingTBAndDesign/AdderWithModPort.sv`,
> `ConnectingTBAndDesign/ArbiterAndTBUsingInterface/`,
> `AdvancedInterfaces/TBWithVirtualInterface.sv`

### Chapter: Procedures
| Slug | Title | Status |
|---|---|---|
| `sv/tasks-functions` | Tasks and Functions | 📝 |

> The `task automatic send(...)` pattern already appears in the
> FSM testbench without explanation. `automatic` keyword, input/output
> arguments, return values.
> Ref: `TasksAndFunctions/` (9 files covering argument directions,
> default values, named arguments, returning arrays)

### Chapter: State Machines
| Slug | Title | Status |
|---|---|---|
| `sv/enums` | typedef enum | ✅ |
| `sv/fsm` | Two-Always Moore FSM | ✅ |
| `sv/mealy-fsm` | Mealy FSM | 📝 |

> Moore-only leaves students unable to recognise the more common Mealy
> pattern in real codebases.

---

## Part 2 — SystemVerilog Assertions

### Chapter: Your First Assertion
| Slug | Title | Status |
|---|---|---|
| `sva/immediate-assert` | Immediate Assertions | ✅ |
| `sva/sequence-basics` | Sequences and Properties | ✅ |

### Chapter: Clock Delay & Sequences
| Slug | Title | Status |
|---|---|---|
| `sva/clock-delay` | Clock Delay ##m and ##[m:n] | ✅ |
| `sva/consecutive-rep` | Consecutive Repetition [*m] | ✅ |
| `sva/nonconsec-rep` | Goto Repetition [->m] | ✅ |
| `sva/sequence-ops` | Sequence Composition (and/or/intersect) | 📝 |

> Without `and`/`or` you cannot write multi-condition concurrent specs.
> `first_match` is also useful when combined with `[m:n]` ranges.

### Chapter: Properties & Implication
| Slug | Title | Status |
|---|---|---|
| `sva/implication` | Implication: \|->, \|=> | ✅ |
| `sva/req-ack` | Request / Acknowledge | ✅ |
| `sva/disable-iff` | disable iff — Reset Handling | ✅ |

### Chapter: Sampled Value Functions
| Slug | Title | Status |
|---|---|---|
| `sva/rose-fell` | $rose and $fell | ✅ |
| `sva/stable-past` | $stable and $past | ✅ |
| `sva/isunknown` | $isunknown — X/Z Detection | 📝 |

> Detecting X-propagation is an important simulation-correctness check.
> Ref: `TipsAndTricks/IsUnknownFunction.sv`

### Chapter: Coverage
| Slug | Title | Status |
|---|---|---|
| `sva/cover-property` | cover property | ✅ |
| `sva/assume-property` | assume property — Formal Verification | 📝 |

> **Critical gap.** `assume` is the third member of the assert/cover/assume
> triad and is the gateway to formal verification (Jasper, VC Formal,
> Symbiyosys). At minimum: what it means, how it constrains the environment
> during model checking, and how the same property file is reused for both
> simulation and formal runs.

### Chapter: Advanced Properties
| Slug | Title | Status |
|---|---|---|
| `sva/local-vars` | Local Variables in Sequences | ✅ |
| `sva/onehot` | $onehot, $onehot0, $countones | ✅ |
| `sva/bind` | bind — Non-Invasive Assertion Attachment | 📝 |

> `bind` lets you attach a checker module to any module without modifying
> it — essential for asserting third-party or locked IP.

---

## Part 3 — Universal Verification Methodology

### Chapter: UVM Foundations
| Slug | Title | Status |
|---|---|---|
| `uvm/reporting` | The First UVM Test | ✅ |
| `uvm/seq-item` | Sequence Items | ✅ |

### Chapter: Stimulus
| Slug | Title | Status |
|---|---|---|
| `uvm/sequence` | Sequences | ✅ |
| `uvm/driver` | The Driver | ✅ |
| `uvm/constrained-random` | Constrained-Random Scenarios | 📝 |

> Build on the existing seq_item lesson: `randomize() with {}` inline
> overrides, weighted distributions (`dist`), `solve…before`, turning
> constraints on/off with `constraint_mode()`.
> Ref: `Randomization/RandomizeWith.sv`, `Randomization/SolveBefore1.sv`,
> `Randomization/TurnConstarintsOnOff.sv`,
> `Randomization/Distributions/`

### Chapter: Checking
| Slug | Title | Status |
|---|---|---|
| `uvm/monitor` | Monitor and Scoreboard | ✅ |
| `uvm/env` | Environment and Test | ✅ |

### Chapter: Functional Coverage *(entirely missing)*
| Slug | Title | Status |
|---|---|---|
| `uvm/covergroup` | covergroup and coverpoint | 📝 |
| `uvm/cross-coverage` | Cross Coverage | 📝 |
| `uvm/coverage-driven` | Coverage-Driven Verification | 📝 |

> **The single biggest gap in the tutorial.** Functional coverage is *why*
> UVM exists — random stimulus is useless without a measure of what has
> been exercised. Three lessons minimum:
>
> 1. `covergroup` / `coverpoint` / bins — write a covergroup for the
>    adder (cover `a` in ranges 0–63, 64–127, 128–255; same for `b`).
> 2. `cross` — cross `a_cp` × `b_cp`; understand the coverage hole.
> 3. Coverage-driven loop — run sequences until coverage hits 100 %.
>
> Ref: `Coverage/CrossCoverage.sv`, `Coverage/CrossCoverageTechniques.sv`,
> `Coverage/ConditionalCoverage.sv`, `Coverage/WeightedCoverage.sv`,
> `Coverage/CoverGroupInClass/`, `Coverage/FunctionalCoverageExample/`

### Chapter: Advanced UVM
| Slug | Title | Status |
|---|---|---|
| `uvm/factory-override` | Factory Overrides | 📝 |
| `uvm/virtual-seq` | Virtual Sequences | 💡 |
| `uvm/ral` | Register Abstraction Layer (RAL) | 💡 |

> **Factory overrides** are the most important "advanced" topic here —
> factory registration is already taught but the payoff (swap a class at
> test level without touching the sequence) is never shown.
> Ref: `AdvancedOOP/GeneratorFactoryPattern.sv`,
> `AdvancedOOP/InjectingExtendedTransaction.sv`

---

## Part 4 — SystemVerilog for Verification (TB-focused SV) *(not yet started)*

This material lives between Part 1 (RTL SV) and Part 3 (UVM) and is
largely what the reference repo covers. It could be a new Part 2, pushing
the current SVA content to Part 3 and UVM to Part 4.

### Chapter: OOP Fundamentals
| Slug | Title | Status |
|---|---|---|
| `tb/classes` | Classes and Objects | 📝 |
| `tb/inheritance` | Inheritance and Polymorphism | 📝 |
| `tb/callbacks` | Callbacks | 💡 |

> Ref: `OOP/FirstClass.sv`, `OOP/GoodGenerator.sv`,
> `AdvancedOOP/Inheritance.sv`, `AdvancedOOP/CallBacks.sv`

### Chapter: Randomization
| Slug | Title | Status |
|---|---|---|
| `tb/rand-basics` | rand, randc, and constraints | 📝 |
| `tb/rand-advanced` | Constraint Techniques | 💡 |

> Ref: `Randomization/SimpleRandomClass.sv`,
> `Randomization/ImplicationAndBidirectional.sv`

### Chapter: Dynamic Data Structures
| Slug | Title | Status |
|---|---|---|
| `tb/dyn-arrays` | Dynamic Arrays and Queues | 📝 |
| `tb/assoc-arrays` | Associative Arrays | 📝 |

> Ref: `Arrays/DynamicArrays.sv`, `Arrays/AssociativeArrays.sv`,
> `Queues/Queue1.sv`–`Queue3.sv`

### Chapter: Concurrency
| Slug | Title | Status |
|---|---|---|
| `tb/fork-join` | fork/join and fork/join_any | 📝 |
| `tb/events` | Events and Semaphores | 📝 |
| `tb/mailbox` | Mailboxes | 📝 |

> Ref: `ThreadsAndInterProcessCommunication/Threads/`,
> `ThreadsAndInterProcessCommunication/Events/`,
> `ThreadsAndInterProcessCommunication/Semaphores/`,
> `ThreadsAndInterProcessCommunication/Mailbox/`

---

## Priority Order

Based on dependencies and impact, the recommended order for new lessons:

1. `sv/tasks-functions` — used but never taught; blocks FSM TB understanding
2. `sv/interfaces` — used but never taught; blocks all UVM lessons
3. `uvm/covergroup` + `uvm/cross-coverage` + `uvm/coverage-driven` — the largest functional gap
4. `sva/assume-property` — unlocks formal verification narrative
5. `sv/packed-structs` + `sv/arrays-static` — essential RTL data types
6. `tb/classes` + `tb/rand-basics` — bridge SV→UVM gap; also prerequisite for `uvm/factory-override`
7. `uvm/factory-override` — completes the factory story begun in seq-item
8. `sv/generate` + `sv/mealy-fsm` — fills RTL gaps
9. `tb/fork-join` + `tb/mailbox` + `tb/events` — TB concurrency model
10. Remainder (optional/stretch) as bandwidth allows
