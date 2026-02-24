/**
 * Full-tutorial QA: every lesson → solve → run/verify → no errors.
 * Lessons are visited by URL index so navigation is fast and reliable.
 */
import { test, expect } from '@playwright/test';

// One entry per lesson in the order they appear in the app.
// runner: 'sim' | 'bmc' | 'lec' | 'both' | 'cocotb'
const LESSONS = [
  { title: 'Welcome',                                     runner: 'sim'    },
  { title: 'Modules and Ports',                           runner: 'sim'    },
  { title: 'always_comb and case',                        runner: 'sim'    },
  { title: 'Priority Encoder',                            runner: 'sim'    },
  { title: 'Flip-Flops with always_ff',                   runner: 'sim'    },
  { title: 'Up-Counter',                                  runner: 'sim'    },
  { title: 'Parameters and localparam',                   runner: 'sim'    },
  { title: 'Interfaces and modport',                      runner: 'sim'    },
  { title: 'Tasks and Functions',                         runner: 'sim'    },
  { title: 'typedef enum',                                runner: 'sim'    },
  { title: 'Two-Always Moore FSM',                        runner: 'sim'    },
  { title: 'covergroup and coverpoint',                   runner: 'sim'    },
  { title: 'Bins and ignore_bins',                        runner: 'sim'    },
  { title: 'Cross coverage',                              runner: 'sim'    },
  { title: 'Your First cocotb Test',                      runner: 'cocotb' },
  { title: 'Clock and Timing',                            runner: 'cocotb' },
  { title: 'Immediate Assertions',                        runner: 'bmc'    },
  { title: 'Concurrent Assertions in Simulation',         runner: 'sim'    },
  { title: 'Vacuous Pass',                                runner: 'sim'    },
  { title: '$isunknown — Detecting X and Z',              runner: 'sim'    },
  { title: 'Sequences and Properties',                    runner: 'bmc'    },
  { title: 'Implication: |-> and |=>',                   runner: 'bmc'    },
  { title: 'Bounded Model Checking',                      runner: 'bmc'    },
  { title: 'Clock Delay ##m and ##[m:n]',                 runner: 'bmc'    },
  { title: '$rose and $fell',                             runner: 'bmc'    },
  { title: 'Request / Acknowledge',                       runner: 'bmc'    },
  { title: 'Consecutive Repetition [*m]',                 runner: 'bmc'    },
  { title: 'Goto Repetition [->m]',                       runner: 'bmc'    },
  { title: 'Non-Consecutive Equal Repetition [=m]',       runner: 'bmc'    },
  { title: 'throughout — Stability During a Sequence',    runner: 'bmc'    },
  { title: 'Sequence Composition: intersect, within, and, or', runner: 'bmc' },
  { title: '$stable and $past',                           runner: 'bmc'    },
  { title: '$changed and $sampled',                       runner: 'bmc'    },
  { title: 'disable iff — Reset Handling',                runner: 'bmc'    },
  { title: 'Aborting Properties: reject_on and accept_on', runner: 'bmc'  },
  { title: 'cover property',                              runner: 'bmc'    },
  { title: 'Local Variables in Sequences',                runner: 'bmc'    },
  { title: '$onehot, $onehot0, $countones',               runner: 'bmc'    },
  { title: '.triggered — Sequence Endpoint Detection',    runner: 'bmc'    },
  { title: 'the checker Construct',                       runner: 'bmc'    },
  { title: 'Recursive Properties',                        runner: 'bmc'    },
  { title: 'always and s_eventually',                     runner: 'bmc'    },
  { title: 'until and s_until',                           runner: 'bmc'    },
  { title: 'assume property',                             runner: 'both'   },
  { title: 'Logical Equivalence Checking',                runner: 'lec'    },
  { title: 'The First UVM Test',                          runner: 'sim'    },
  { title: 'Sequence Items',                              runner: 'sim'    },
  { title: 'Sequences',                                   runner: 'sim'    },
  { title: 'The Driver',                                  runner: 'sim'    },
  { title: 'Monitor and Scoreboard',                      runner: 'sim'    },
  { title: 'Environment and Test',                        runner: 'sim'    },
  { title: 'Functional Coverage',                         runner: 'sim'    },
  { title: 'Cross Coverage',                              runner: 'sim'    },
  { title: 'Coverage-Driven Verification',                runner: 'sim'    },
];

for (const [index, lesson] of LESSONS.entries()) {
  test(`[${index}] ${lesson.title}`, async ({ page }) => {
    await page.goto(`/?lesson=${index}`);

    // Verify we landed on the right lesson
    await expect(page.getByTestId('lesson-title')).toHaveText(lesson.title, { timeout: 10_000 });

    // Apply solution
    const solveBtn = page.getByTestId('solve-button');
    if (await solveBtn.count() > 0) {
      await solveBtn.click();
      await expect(solveBtn).toHaveText('reset', { timeout: 5_000 });
    }

    const logs = page.getByTestId('runtime-logs');

    if (lesson.runner === 'sim' || lesson.runner === 'cocotb' || lesson.runner === 'both') {
      await page.getByTestId('run-button').click();
      await expect(logs).not.toContainText('exit code: 1', { timeout: 120_000 });
      // Confirm a tool actually ran
      const toolRan = await Promise.race([
        expect(logs).toContainText('$ circt-sim', { timeout: 120_000 }).then(() => true).catch(() => false),
        expect(logs).toContainText('$ cocotb',    { timeout: 120_000 }).then(() => true).catch(() => false),
      ]);
      // At least one of circt-sim or cocotb must appear
      const logText = await logs.innerText();
      const ran = logText.includes('$ circt-sim') || logText.includes('$ cocotb') || logText.includes('cocotb');
      expect(ran, `No sim tool ran for lesson "${lesson.title}": ${logText.slice(0, 300)}`).toBe(true);
    }

    if (lesson.runner === 'bmc' || lesson.runner === 'lec' || lesson.runner === 'both') {
      const verifyBtn = page.getByTestId('verify-button');
      await verifyBtn.click();
      await expect(logs).not.toContainText('exit code: 1', { timeout: 120_000 });
      const logText = await logs.innerText();
      const ran = logText.includes('$ circt-bmc') || logText.includes('$ circt-lec');
      expect(ran, `No formal tool ran for lesson "${lesson.title}": ${logText.slice(0, 300)}`).toBe(true);
    }
  });
}
