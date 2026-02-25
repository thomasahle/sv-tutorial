/**
 * Comprehensive solution runner: applies the golden solution for every lesson
 * and asserts that the output matches expectations.
 *
 * Expectations by runner type:
 *   sim / (none) — run button: no compilation exit-code errors
 *   bmc          — verify button: no errors + z3 ran ([z3] appears)
 *   both         — verify button: same as bmc
 *   lec          — verify button: [z3] unsat (circuits proved equivalent)
 *   cocotb       — run button (labelled "test"): no errors
 *
 * expectUnsat: true  — additionally asserts [z3] unsat.
 *   Only set for lessons whose solution module has real design logic that
 *   enforces the properties (formal-intro counter, formal-assume FSM, lec
 *   equivalence check). These are the only cases where circt-bmc can prove
 *   unsat because the design itself rules out counterexamples.
 *
 * expectUnsat: false — only checks that [z3] ran and exit codes are 0.
 *   Property-only modules (checker modules with free input ports and
 *   assertions but no design logic) always produce [z3] sat because BMC
 *   can trivially assign free inputs to violate any non-trivial property.
 *   That is expected and correct behaviour for these lessons.
 */

import { test, expect } from '@playwright/test';

// ── Navigation helper ─────────────────────────────────────────────────────────

async function goToLesson(page, chapterName, lessonName) {
  // Navigate to the first lesson directly rather than '/' to avoid the
  // SPA-fallback → SvelteKit client-side redirect timing issue where
  // page.goto('/') returns before the redirect to /lesson/sv/welcome completes.
  await page.goto('/lesson/sv/welcome');
  // Clear stored workspaces so each test starts from the starter files,
  // not a workspace saved by a previous test run.
  await page.evaluate(() => {
    for (const key of Object.keys(localStorage)) {
      if (key.startsWith('svt:')) localStorage.removeItem(key);
    }
  });

  // Wait for the Svelte $effect to expand the active chapter (Introduction),
  // which makes at least one lesson button (button[data-active]) appear.
  // This ensures hydration + effects have settled before we interact.
  await page.locator('button[data-active]').first().waitFor({ timeout: 5_000 });

  // Lesson buttons carry a data-active attribute; chapter buttons do not.
  // Using this selector avoids strict-mode violations when a chapter title
  // partially matches a lesson name (e.g. "Core Sequences" vs "Sequences")
  // or when a chapter and lesson share the same name ("Functional Coverage").
  const lessonBtn = page.locator('button[data-active]').filter({ hasText: lessonName });

  // Only click the chapter button if the lesson is not already visible.
  // Target only chapter buttons (no data-active) to avoid partial-name
  // collisions between chapter and lesson button text.
  if ((await lessonBtn.count()) === 0) {
    await page.locator('button:not([data-active])').filter({ hasText: chapterName }).click();
  }

  await lessonBtn.click();
  await expect(page.getByRole('heading', { level: 2, name: lessonName })).toBeVisible();
}

// ── Lesson registry ───────────────────────────────────────────────────────────
// Derived from src/lessons/index.js hierarchy + per-lesson meta.json.
// runner: null  → simulation (run button, no verify button)
// runner: 'bmc' → bounded model checking (verify button only)
// runner: 'both'→ sim + bmc (both buttons; solution test uses verify)
// runner: 'lec' → logical equivalence check (verify button; expects [z3] unsat)
// runner: 'cocotb' → cocotb Python tests (run/test button)
//
// expectUnsat: true  → module has design logic; circt-bmc should prove unsat.
// expectUnsat: false → property-only module; [z3] sat is expected and OK.

const LESSONS = [
  // ── SystemVerilog Basics ────────────────────────────────────────────────────
  { chapter: 'Introduction',            title: 'Welcome',                                       runner: null },
  { chapter: 'Introduction',            title: 'Modules and Ports',                             runner: null },
  { chapter: 'Combinational Logic',     title: 'always_comb and case',                          runner: null },
  { chapter: 'Combinational Logic',     title: 'Priority Encoder',                              runner: null },
  { chapter: 'Sequential Logic',        title: 'Flip-Flops with always_ff',                     runner: null },
  { chapter: 'Sequential Logic',        title: 'Up-Counter',                                    runner: null },
  { chapter: 'Parameterized Modules',   title: 'Parameters and localparam',                     runner: null },
  { chapter: 'Interfaces & Procedures', title: 'Interfaces and modport',                        runner: null },
  { chapter: 'Interfaces & Procedures', title: 'Tasks and Functions',                           runner: null },
  { chapter: 'State Machines',          title: 'typedef enum',                                  runner: null },
  { chapter: 'State Machines',          title: 'Two-Always Moore FSM',                          runner: null },
  { chapter: 'Covergroups',             title: 'covergroup and coverpoint',                     runner: null },
  { chapter: 'Covergroups',             title: 'Bins and ignore_bins',                          runner: null },
  { chapter: 'Covergroups',             title: 'Cross coverage',                                runner: null },

  // ── SystemVerilog Assertions ────────────────────────────────────────────────
  { chapter: 'Runtime Assertions',        title: 'Concurrent Assertions in Simulation',          runner: null, expectAssertionFail: true },
  { chapter: 'Runtime Assertions',        title: 'Vacuous Pass',                                 runner: null },
  { chapter: 'Runtime Assertions',        title: '$isunknown — Detecting X and Z',               runner: null },
  { chapter: 'Your First Formal Assertion', title: 'Immediate Assertions',                       runner: 'bmc', expectUnsat: false },
  { chapter: 'Your First Formal Assertion', title: 'Sequences and Properties',                   runner: 'bmc', expectUnsat: false },
  { chapter: 'Implication & BMC',       title: 'Implication: |-> and |=>',                     runner: 'bmc', expectUnsat: false },
  // formal-intro: up-counter design — reset guarantees cnt == 0 → proved unsat
  { chapter: 'Implication & BMC',       title: 'Bounded Model Checking',                        runner: 'bmc', expectUnsat: true },
  { chapter: 'Core Sequences',          title: 'Clock Delay ##m and ##[m:n]',                   runner: 'bmc', expectUnsat: false },
  { chapter: 'Core Sequences',          title: '$rose and $fell',                               runner: 'bmc', expectUnsat: false },
  { chapter: 'Core Sequences',          title: 'Request / Acknowledge',                         runner: 'bmc', expectUnsat: false },
  { chapter: 'Repetition Operators',    title: 'Consecutive Repetition [*m]',                   runner: 'bmc', expectUnsat: false },
  { chapter: 'Repetition Operators',    title: 'Goto Repetition [->m]',                         runner: 'bmc', expectUnsat: false },
  { chapter: 'Repetition Operators',    title: 'Non-Consecutive Equal Repetition [=m]',         runner: 'bmc', expectUnsat: false },
  { chapter: 'Sequence Operators',      title: 'throughout — Stability During a Sequence',      runner: 'bmc', expectUnsat: false },
  { chapter: 'Sequence Operators',      title: 'Sequence Composition: intersect, within, and, or', runner: 'bmc', expectUnsat: false },
  { chapter: 'Sampled Value Functions', title: '$stable and $past',                             runner: 'bmc', expectUnsat: false },
  { chapter: 'Sampled Value Functions', title: '$changed and $sampled',                         runner: 'bmc', expectUnsat: false },
  { chapter: 'Protocols & Coverage',    title: 'disable iff — Reset Handling',                  runner: 'bmc', expectUnsat: false },
  { chapter: 'Protocols & Coverage',    title: 'Aborting Properties: reject_on and accept_on',  runner: 'bmc', expectUnsat: false },
  { chapter: 'Protocols & Coverage',    title: 'cover property',                                runner: 'bmc', expectUnsat: false },
  { chapter: 'Advanced Properties',     title: 'Local Variables in Sequences',                  runner: 'bmc', expectUnsat: false },
  { chapter: 'Advanced Properties',     title: '$onehot, $onehot0, $countones',                 runner: 'bmc', expectUnsat: false },
  { chapter: 'Advanced Properties',     title: '.triggered — Sequence Endpoint Detection',      runner: 'bmc', expectUnsat: false },
  { chapter: 'Advanced Properties',     title: 'The checker Construct',                         runner: 'bmc', expectUnsat: false },
  { chapter: 'Advanced Properties',     title: 'Recursive Properties',                          runner: 'bmc', expectUnsat: false },
  // formal-assume: traffic-light FSM + assume → state space constrained → proved unsat
  { chapter: 'Formal Verification',     title: 'assume property',                               runner: 'both', expectUnsat: true },
  { chapter: 'Formal Verification',     title: 'always and s_eventually',                       runner: 'bmc', expectUnsat: false },
  { chapter: 'Formal Verification',     title: 'until and s_until',                             runner: 'bmc', expectUnsat: false },
  // lec: two circuit implementations compared — proved equivalent → unsat
  { chapter: 'Formal Verification',     title: 'Logical Equivalence Checking',                  runner: 'lec', expectUnsat: true },

  // ── UVM ────────────────────────────────────────────────────────────────────
  { chapter: 'UVM Foundations',    title: 'The First UVM Test',            runner: null },
  { chapter: 'UVM Foundations',    title: 'Sequence Items',                runner: null },
  { chapter: 'Stimulus',           title: 'Sequences',                     runner: null },
  { chapter: 'Stimulus',           title: 'The Driver',                    runner: null },
  { chapter: 'Checking',           title: 'Monitor and Scoreboard',        runner: null },
  { chapter: 'Checking',           title: 'Environment and Test',          runner: null },
  { chapter: 'Functional Coverage', title: 'Functional Coverage',          runner: null },
  { chapter: 'Functional Coverage', title: 'Cross Coverage',               runner: null },
  { chapter: 'Functional Coverage', title: 'Coverage-Driven Verification', runner: null },

  // ── cocotb ─────────────────────────────────────────────────────────────────
  { chapter: 'cocotb Basics', title: 'Your First cocotb Test', runner: 'cocotb' },
  { chapter: 'cocotb Basics', title: 'Clock and Timing',        runner: 'cocotb' },
];

// ── Shared assertions ─────────────────────────────────────────────────────────

const COMPILE_TIMEOUT = 90_000;
const Z3_TIMEOUT      = 120_000;

function assertNoCompileError(logs) {
  return expect(logs).not.toContainText('# circt-verilog exit code: 1', { timeout: COMPILE_TIMEOUT });
}

// ── Tests ─────────────────────────────────────────────────────────────────────

for (const lesson of LESSONS) {
  test(`[${lesson.runner ?? 'sim'}] ${lesson.title}`, async ({ page }) => {
    await goToLesson(page, lesson.chapter, lesson.title);

    // Open the gear menu then apply the solution.
    await page.getByTestId('options-button').click();
    await page.getByTestId('solve-button').click();

    const logs = page.getByTestId('runtime-logs');

    if (lesson.runner === 'lec') {
      await page.getByTestId('verify-button').click();
      await assertNoCompileError(logs);
      await expect(logs).not.toContainText('# circt-lec exit code: 1', { timeout: COMPILE_TIMEOUT });
      await expect(logs).toContainText('unsat', { timeout: Z3_TIMEOUT });

    } else if (lesson.runner === 'bmc' || lesson.runner === 'both') {
      await page.getByTestId('verify-button').click();
      await assertNoCompileError(logs);
      await expect(logs).not.toContainText('# circt-bmc exit code: 1', { timeout: COMPILE_TIMEOUT });
      await expect(logs).toContainText('[z3]', { timeout: Z3_TIMEOUT });
      if (lesson.expectUnsat) {
        await expect(logs).toContainText('[z3] unsat', { timeout: Z3_TIMEOUT });
        await expect(logs).not.toContainText('[z3] sat');
      }

    } else if (lesson.runner === 'cocotb') {
      await page.getByTestId('run-button').click();
      await assertNoCompileError(logs);
      await expect(logs).not.toContainText('exit code: 1', { timeout: COMPILE_TIMEOUT });

    } else {
      // sim (runner: null)
      await page.getByTestId('run-button').click();
      await assertNoCompileError(logs);
      if (lesson.expectAssertionFail) {
        await expect(logs).toContainText('SVA assertion failed', { timeout: COMPILE_TIMEOUT });
      }
    }
  });
}
