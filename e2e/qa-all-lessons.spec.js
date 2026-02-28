/**
 * Full-tutorial QA: every lesson → solve → run/verify → no errors.
 * Lessons are visited by their slug URL (/lesson/part/name) for reliable navigation.
 */
import { test, expect } from '@playwright/test';

const base = process.env.VITE_BASE?.replace(/\/$/, '') ?? '';

// One entry per lesson in the exact order they appear in the app (matches index.js).
// runner: 'sim' | 'bmc' | 'lec' | 'both' | 'cocotb'
const LESSONS = [
  // ── SystemVerilog Basics ──────────────────────────────────────────────────────
  { title: 'Welcome',                                          slug: 'sv/welcome',           runner: 'sim'    },
  { title: 'Modules and Ports',                                slug: 'sv/modules-and-ports', runner: 'sim'    },
  { title: 'always_comb and case',                             slug: 'sv/always-comb',       runner: 'sim'    },
  { title: 'Flip-Flops with always_ff',                        slug: 'sv/always-ff',         runner: 'sim'    },
  { title: 'Up-Counter',                                       slug: 'sv/counter',           runner: 'sim'    },
  { title: 'Parameters',                                       slug: 'sv/parameters',        runner: 'sim'    },
  { title: 'Packed Structs and Unions',                        slug: 'sv/packed-structs',    runner: 'sim'    },
  { title: 'Interfaces',                                       slug: 'sv/interfaces',        runner: 'sim'    },
  { title: 'Modports',                                          slug: 'sv/modports',          runner: 'sim'    },
  { title: 'Tasks and Functions',                              slug: 'sv/tasks-functions',   runner: 'sim'    },
  { title: 'typedef enum',                                     slug: 'sv/enums',             runner: 'sim'    },
  { title: 'Two-Always Moore FSM',                             slug: 'sv/fsm',               runner: 'sim'    },
  { title: 'covergroup and coverpoint',                        slug: 'sv/covergroup-basics', runner: 'sim'    },
  { title: 'Bins and ignore_bins',                             slug: 'sv/coverpoint-bins',   runner: 'sim'    },
  { title: 'Cross coverage',                                   slug: 'sv/cross-coverage',    runner: 'sim'    },
  // ── SystemVerilog Assertions ──────────────────────────────────────────────────
  { title: 'Concurrent Assertions in Simulation',              slug: 'sva/concurrent-sim',   runner: 'sim'    },
  { title: 'Vacuous Pass',                                     slug: 'sva/vacuous-pass',     runner: 'sim'    },
  { title: '$isunknown — Detecting X and Z',                   slug: 'sva/isunknown',        runner: 'sim'    },
  { title: 'Immediate Assertions',                             slug: 'sva/immediate-assert', runner: 'bmc'    },
  { title: 'Sequences and Properties',                         slug: 'sva/sequence-basics',  runner: 'bmc'    },
  { title: 'Implication: |-> and |=>',                        slug: 'sva/implication',      runner: 'bmc'    },
  { title: 'Bounded Model Checking',                           slug: 'sva/formal-intro',     runner: 'bmc'    },
  { title: 'Clock Delay ##m and ##[m:n]',                      slug: 'sva/clock-delay',      runner: 'bmc'    },
  { title: '$rose and $fell',                                  slug: 'sva/rose-fell',        runner: 'bmc'    },
  { title: 'Request / Acknowledge',                            slug: 'sva/req-ack',          runner: 'bmc'    },
  { title: 'Consecutive Repetition [*m]',                      slug: 'sva/consecutive-rep',  runner: 'bmc'    },
  { title: 'Goto Repetition [->m]',                            slug: 'sva/nonconsec-rep',    runner: 'bmc'    },
  { title: 'Non-Consecutive Equal Repetition [=m]',            slug: 'sva/nonconsec-eq',     runner: 'bmc'    },
  { title: 'throughout — Stability During a Sequence',         slug: 'sva/throughout',       runner: 'bmc'    },
  { title: 'Sequence Composition: intersect, within, and, or', slug: 'sva/sequence-ops',     runner: 'bmc'    },
  { title: 'Sequence Formal Arguments',                        slug: 'sva/seq-args',         runner: 'bmc'    },
  { title: '$stable and $past',                                slug: 'sva/stable-past',      runner: 'bmc'    },
  { title: '$changed and $sampled',                            slug: 'sva/changed',          runner: 'bmc'    },
  { title: 'disable iff — Reset Handling',                     slug: 'sva/disable-iff',      runner: 'bmc'    },
  { title: 'Aborting Properties: reject_on and accept_on',     slug: 'sva/abort',            runner: 'bmc'    },
  { title: 'cover property',                                   slug: 'sva/cover-property',   runner: 'bmc'    },
  { title: 'Local Variables in Sequences',                     slug: 'sva/local-vars',       runner: 'bmc'    },
  { title: '$onehot, $onehot0, $countones',                    slug: 'sva/onehot',           runner: 'bmc'    },
  { title: '.triggered — Sequence Endpoint Detection',         slug: 'sva/triggered',        runner: 'bmc'    },
  { title: 'The checker Construct',                            slug: 'sva/checker',          runner: 'bmc'    },
  { title: 'Recursive Properties',                             slug: 'sva/recursive',        runner: 'bmc'    },
  { title: 'assume property',                                  slug: 'sva/formal-assume',    runner: 'both'   },
  { title: 'always and s_eventually',                          slug: 'sva/always-eventually',runner: 'bmc'    },
  { title: 'until and s_until',                                slug: 'sva/until',            runner: 'bmc'    },
  { title: 'Logical Equivalence Checking',                     slug: 'sva/lec',              runner: 'lec'    },
  // ── UVM ──────────────────────────────────────────────────────────────────────
  { title: 'The First UVM Test',                               slug: 'uvm/reporting',        runner: 'sim'    },
  { title: 'Sequence Items',                                   slug: 'uvm/seq-item',         runner: 'sim'    },
  { title: 'Sequences',                                        slug: 'uvm/sequence',         runner: 'sim'    },
  { title: 'The Driver',                                       slug: 'uvm/driver',           runner: 'sim'    },
  { title: 'Constrained-Random Scenarios',                     slug: 'uvm/constrained-random', runner: 'sim'  },
  { title: 'Monitor and Scoreboard',                           slug: 'uvm/monitor',          runner: 'sim'    },
  { title: 'Environment and Test',                             slug: 'uvm/env',              runner: 'sim'    },
  { title: 'Functional Coverage',                              slug: 'uvm/covergroup',       runner: 'sim'    },
  { title: 'Cross Coverage',                                   slug: 'uvm/cross-coverage',   runner: 'sim'    },
  { title: 'Coverage-Driven Verification',                     slug: 'uvm/coverage-driven',  runner: 'sim'    },
  { title: 'Factory Overrides',                                slug: 'uvm/factory-override', runner: 'sim'    },
  // ── cocotb ───────────────────────────────────────────────────────────────────
  { title: 'Your First cocotb Test',                           slug: 'cocotb/first-test',    runner: 'cocotb' },
  { title: 'Clock and Timing',                                 slug: 'cocotb/clock-and-timing', runner: 'cocotb' },
];

for (const [index, lesson] of LESSONS.entries()) {
  test(`[${String(index + 1).padStart(2)}] ${lesson.title}`, async ({ page }) => {
    const [part, name] = lesson.slug.split('/');
    await page.goto(`${base}/lesson/${part}/${name}`);
    await expect(page.getByTestId('lesson-title')).toHaveText(lesson.title, { timeout: 10_000 });

    // Apply the solution
    await page.getByTestId('options-button').click();
    const solveBtn = page.getByTestId('solve-button');
    if (await solveBtn.count() > 0) {
      const label = ((await solveBtn.textContent()) ?? '').trim();
      if (label !== 'Reset to starter') await solveBtn.click();
      else await page.keyboard.press('Escape');
    } else {
      await page.keyboard.press('Escape');
    }

    const logs = page.getByTestId('runtime-logs');

    // Run simulation (sim / cocotb / both)
    if (lesson.runner === 'sim' || lesson.runner === 'cocotb' || lesson.runner === 'both') {
      await page.getByTestId('run-button').click();
      await expect(logs).not.toContainText('exit code: 1', { timeout: 120_000 });
      // Confirm a simulation tool actually executed
      await expect(logs).toContainText('$ circt', { timeout: 120_000 });
    }

    // Run formal / LEC (bmc / lec / both)
    if (lesson.runner === 'bmc' || lesson.runner === 'lec' || lesson.runner === 'both') {
      await page.getByTestId('verify-button').click();
      await expect(logs).not.toContainText('exit code: 1', { timeout: 120_000 });
      await expect(logs).toContainText('$ circt', { timeout: 120_000 });
    }
  });
}
