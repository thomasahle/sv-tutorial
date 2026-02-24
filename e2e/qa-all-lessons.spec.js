/**
 * Full-tutorial QA: every lesson → solve → run/verify → no errors.
 * Lessons are visited by URL index (?lesson=N, 1-based) for reliable navigation.
 */
import { test, expect } from '@playwright/test';

// One entry per lesson in the exact order they appear in the app (matches index.js).
// runner: 'sim' | 'bmc' | 'lec' | 'both' | 'cocotb'
const LESSONS = [
  // ── SystemVerilog Basics ──────────────────────────────────────────────────────
  { title: 'Welcome',                                          runner: 'sim'    },
  { title: 'Modules and Ports',                                runner: 'sim'    },
  { title: 'always_comb and case',                             runner: 'sim'    },
  { title: 'Priority Encoder',                                 runner: 'sim'    },
  { title: 'Flip-Flops with always_ff',                        runner: 'sim'    },
  { title: 'Up-Counter',                                       runner: 'sim'    },
  { title: 'Parameters and localparam',                        runner: 'sim'    },
  { title: 'Interfaces and modport',                           runner: 'sim'    },
  { title: 'Tasks and Functions',                              runner: 'sim'    },
  { title: 'typedef enum',                                     runner: 'sim'    },
  { title: 'Two-Always Moore FSM',                             runner: 'sim'    },
  { title: 'covergroup and coverpoint',                        runner: 'sim'    },
  { title: 'Bins and ignore_bins',                             runner: 'sim'    },
  { title: 'Cross coverage',                                   runner: 'sim'    },
  // ── SystemVerilog Assertions ──────────────────────────────────────────────────
  { title: 'Concurrent Assertions in Simulation',              runner: 'sim'    },
  { title: 'Vacuous Pass',                                     runner: 'sim'    },
  { title: '$isunknown — Detecting X and Z',                   runner: 'sim'    },
  { title: 'Immediate Assertions',                             runner: 'bmc'    },
  { title: 'Sequences and Properties',                         runner: 'bmc'    },
  { title: 'Implication: |-> and |=>',                        runner: 'bmc'    },
  { title: 'Bounded Model Checking',                           runner: 'bmc'    },
  { title: 'Clock Delay ##m and ##[m:n]',                      runner: 'bmc'    },
  { title: '$rose and $fell',                                  runner: 'bmc'    },
  { title: 'Request / Acknowledge',                            runner: 'bmc'    },
  { title: 'Consecutive Repetition [*m]',                      runner: 'bmc'    },
  { title: 'Goto Repetition [->m]',                            runner: 'bmc'    },
  { title: 'Non-Consecutive Equal Repetition [=m]',            runner: 'bmc'    },
  { title: 'throughout — Stability During a Sequence',         runner: 'bmc'    },
  { title: 'Sequence Composition: intersect, within, and, or', runner: 'bmc'    },
  { title: '$stable and $past',                                runner: 'bmc'    },
  { title: '$changed and $sampled',                            runner: 'bmc'    },
  { title: 'disable iff — Reset Handling',                     runner: 'bmc'    },
  { title: 'Aborting Properties: reject_on and accept_on',     runner: 'bmc'    },
  { title: 'cover property',                                   runner: 'bmc'    },
  { title: 'Local Variables in Sequences',                     runner: 'bmc'    },
  { title: '$onehot, $onehot0, $countones',                    runner: 'bmc'    },
  { title: '.triggered — Sequence Endpoint Detection',         runner: 'bmc'    },
  { title: 'The checker Construct',                            runner: 'bmc'    },
  { title: 'Recursive Properties',                             runner: 'bmc'    },
  { title: 'assume property',                                  runner: 'both'   },
  { title: 'always and s_eventually',                          runner: 'bmc'    },
  { title: 'until and s_until',                                runner: 'bmc'    },
  { title: 'Logical Equivalence Checking',                     runner: 'lec'    },
  // ── UVM ──────────────────────────────────────────────────────────────────────
  { title: 'The First UVM Test',                               runner: 'sim'    },
  { title: 'Sequence Items',                                   runner: 'sim'    },
  { title: 'Sequences',                                        runner: 'sim'    },
  { title: 'The Driver',                                       runner: 'sim'    },
  { title: 'Monitor and Scoreboard',                           runner: 'sim'    },
  { title: 'Environment and Test',                             runner: 'sim'    },
  { title: 'Functional Coverage',                              runner: 'sim'    },
  { title: 'Cross Coverage',                                   runner: 'sim'    },
  { title: 'Coverage-Driven Verification',                     runner: 'sim'    },
  // ── cocotb ───────────────────────────────────────────────────────────────────
  { title: 'Your First cocotb Test',                           runner: 'cocotb' },
  { title: 'Clock and Timing',                                 runner: 'cocotb' },
];

for (const [index, lesson] of LESSONS.entries()) {
  test(`[${String(index + 1).padStart(2)}] ${lesson.title}`, async ({ page }) => {
    // URL uses 1-based lesson index
    await page.goto(`/?lesson=${index + 1}`);
    await expect(page.getByTestId('lesson-title')).toHaveText(lesson.title, { timeout: 10_000 });

    // Apply the solution
    const solveBtn = page.getByTestId('solve-button');
    if (await solveBtn.count() > 0) {
      await solveBtn.click();
      await expect(solveBtn).toHaveText('reset', { timeout: 5_000 });
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
