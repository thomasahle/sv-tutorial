# Lesson Quality Rubric

Each lesson is scored across 9 dimensions (1–3 each, max 27).
A lesson averaging below 2 (score < 18) has a real problem worth fixing.

Each dimension is grounded in one or more of these five cognitive science effects:

- **Generation effect** — producing an answer beats reading one; even small generation tasks dramatically improve retention
- **Desirable difficulties** — the right amount of struggle improves long-term retention; too easy = forgotten, too hard = disengagement
- **Dual coding** — combining verbal/textual explanation with visual output creates two independent retrieval paths
- **Spaced retrieval** — seeing a concept reused in a new context later strengthens the original memory
- **Emotional engagement** — surprise, curiosity, and "aha" moments improve encoding; meaningless-feeling tasks impede it

---

## Dimensions

### 1. Concept Focus
*Serves: generation effect, cognitive load*

Is the lesson about exactly one new thing?

- **3** — One new language or tool concept; everything else is already familiar from prior lessons
- **2** — One primary concept plus minor supporting detail the student hasn't seen before
- **1** — Multiple new concepts introduced simultaneously; student doesn't know what to focus on

---

### 2. Starter Calibration
*Serves: generation effect, desirable difficulties*

Is the gap between starter and solution the right size and shape?

- **3** — Student writes 5–10 lines across 1–2 files; requires genuine application of exactly the knowledge just taught; achievable without hints; TODO comments describe *what* to do in English, never the code itself
- **2** — Too trivial (fewer than 5 lines, obvious fill-in) or too large (more than ~15 lines, too many files)
- **1** — Starter is essentially complete (student just reads), so sparse the student has no foothold, **or TODO comments contain the exact solution code** (e.g. `// TODO: if (we) mem[addr] <= wdata;`)

---

### 3. Description Quality
*Serves: emotional engagement, cognitive load*

Does the description motivate the concept, scaffold new syntax, and fit on screen?

- **3** — Fits on one screen (two at most); leads with *why this matters* for the SRAM project; raises a question or shows a problem *before* explaining the solution; every non-obvious syntax element introduced in the lesson (new operators, port conventions, signal naming suffixes like `_n`) is explained — either in the description, as an inline code comment, or as a blockquote
- **2** — Explains mechanics clearly but motivation is thin, some new syntax is left unexplained, or the description is too long
- **1** — Reference-doc style; student doesn't know why they're learning this; no connection to the larger project; new syntax is dropped with no explanation

**Convention:** When a lesson introduces a new syntax construct (module, interface, modport, task, etc.), open the description with an abstract template using angle-bracket placeholders (`&lt;name&gt;`, `&lt;signals&gt;`, `N`, `...`) *before* showing the concrete SRAM example. This gives the student a generalizable mental model rather than just a single instance to memorise.

---

### 4. Progression
*Serves: spaced retrieval*

Does the lesson build visibly on prior work?

- **3** — The files the student edits contain familiar patterns from prior lessons (e.g. the same SRAM they wrote two lessons ago); student retrieves and applies prior knowledge in a new context; support files are minimal so the editor isn't cluttered
- **2** — References prior concepts loosely, or reuses prior artifacts but buries them among too many other files
- **1** — Self-contained; no visible connection to prior lessons; student can't see how the pieces fit together

---

### 5. Dual Coding
*Serves: dual coding*

Does running the code encode the concept in two ways — textual and visual — and can the student verify correctness before solving?

- **3** — A `tb.sv` is present in the **starter** files (not just the solution) and prints PASS/FAIL or clearly labelled output so the student can run it *before* solving to see failures and *after* to confirm success; the waveform viewer adds a second retrieval path
- **2** — Testbench exists but is only visible after clicking "solve", or exists in starter but produces output that doesn't help verify correctness (no PASS/FAIL, no expected values shown)
- **1** — No testbench, or testbench produces no meaningful output; student can't tell if their solution is correct without manual inspection

**Requirement:** Every testbench (`tb.sv`, `tb_top.sv`, or equivalent top-level simulation file) **must** print `PASS` (via `$display("PASS")`) **if and only if** the implementation is correct. This single token is used to automatically detect lesson completion. For UVM lessons, use `uvm_report_server::get_server().get_severity_count(UVM_ERROR) == 0` as the correctness condition. For plain SV lessons, check the expected output values explicitly. For observational lessons (SVA assertions, functional coverage) where correctness is binary pass/fail of running the simulation, `$display("PASS")` may be unconditional.

---

### 6. Solution Idiom
*Serves: emotional engagement, real-world relevance*

Is the solution code written the way a working engineer would write it?

- **3** — Code matches real RTL or verification practice; patterns are ones the student will recognise in real codebases
- **2** — Correct but somewhat simplified; a working engineer would restructure it
- **1** — Teaches a bad habit or uses an unidiomatic pattern the student will have to unlearn

---

### 7. Concept Importance
*Serves: emotional engagement*

Is this concept actually used in practical SystemVerilog?

- **3** — Appears constantly in real RTL or verification code; a student who skips this lesson will be confused by real codebases
- **2** — Useful but situational; appears in specialised contexts
- **1** — Rarely seen outside academic exercises; hard to justify its place in the tutorial

---

### 8. Lesson Novelty
*Serves: emotional engagement, desirable difficulties*

Does this lesson feel genuinely new, or like a repeat?

- **3** — The student encounters something they couldn't do before, sees the computer do something they didn't expect, or has a clear "aha" moment; not just the same pattern with new syntax
- **2** — Familiar structure but the new concept is meaningfully different; mild sense of discovery
- **1** — Feels like a repeat of a lesson already covered; student wonders why they're doing this again

---

### 9. Visual Novelty
*Serves: emotional engagement (curiosity gap)*

Does the lesson look different before the student has read a single word?

- **3** — The lesson has a distinct visual identity: an image, diagram, unusual file layout, block quote, or structural variation that triggers curiosity on first glance; student thinks "what is this?" before reading
- **2** — Mostly similar to adjacent lessons in appearance but has at least one visual element that breaks the monotony
- **1** — Visually identical to the surrounding lessons; nothing draws the eye or raises a question

---

## Tracking

Scores are recorded in `CURRICULUM.md` as `total/27` next to each lesson, e.g. `18/27`.
Individual low-scoring dimensions are flagged by number, e.g. `⚠️ 3,5` means description and dual coding need work.
