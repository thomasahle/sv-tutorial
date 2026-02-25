/**
 * Live-site smoke test wrapper — runs selected lessons from solutions.spec.js
 * against https://thomasnormal.github.io/sv-tutorial/
 *
 * Uses the full URL in goto() since the app lives at a sub-path.
 */

import { test, expect } from '@playwright/test';

const BASE = 'https://thomasnormal.github.io/sv-tutorial/';

async function goToLesson(page, chapterName, lessonName) {
  await page.goto(BASE);
  await page.evaluate(() => {
    for (const key of Object.keys(localStorage)) {
      if (key.startsWith('svt:')) localStorage.removeItem(key);
    }
  });

  const lessonBtn = page.locator('button[data-active]').filter({ hasText: lessonName });

  if ((await lessonBtn.count()) === 0) {
    await page.locator('button:not([data-active])').filter({ hasText: chapterName }).click();
  }

  await lessonBtn.click();
  await expect(page.getByRole('heading', { level: 2, name: lessonName })).toBeVisible();
}

const COMPILE_TIMEOUT = 90_000;
const Z3_TIMEOUT      = 120_000;

function assertNoCompileError(logs) {
  return expect(logs).not.toContainText('# circt-verilog exit code: 1', { timeout: COMPILE_TIMEOUT });
}

// Selected lessons covering all runner types
const LESSONS = [
  // sim (runner: null)
  { chapter: 'Introduction',          title: 'Welcome',                                  runner: null },
  { chapter: 'Runtime Assertions',    title: 'Concurrent Assertions in Simulation',       runner: null, expectAssertionFail: true },
  // bmc (runner: bmc)
  { chapter: 'Your First Formal Assertion', title: 'Immediate Assertions',               runner: 'bmc', expectUnsat: false },
  { chapter: 'Core Sequences',        title: 'Clock Delay ##m and ##[m:n]',              runner: 'bmc', expectUnsat: false },
  // both (runner: both)
  { chapter: 'Formal Verification',   title: 'assume property',                          runner: 'both', expectUnsat: true },
  // lec (runner: lec)
  { chapter: 'Formal Verification',   title: 'Logical Equivalence Checking',             runner: 'lec', expectUnsat: true },
  // cocotb
  { chapter: 'cocotb Basics',         title: 'Your First cocotb Test',                  runner: 'cocotb' },
];

for (const lesson of LESSONS) {
  test(`[${lesson.runner ?? 'sim'}] ${lesson.title}`, async ({ page }) => {
    await goToLesson(page, lesson.chapter, lesson.title);

    await page.getByTestId('options-button').click();
    await page.getByTestId('solve-button').click();

    const logs = page.getByTestId('runtime-logs');

    if (lesson.runner === 'lec') {
      await page.getByTestId('verify-button').click();
      await assertNoCompileError(logs);
      await expect(logs).not.toContainText('# circt-lec exit code: 1', { timeout: COMPILE_TIMEOUT });
      await expect(logs).toContainText('[z3] unsat', { timeout: Z3_TIMEOUT });

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
