/**
 * E2E tests for all UVM lessons (circt-verilog -> circt-sim with full UVM).
 */
import { test, expect } from '@playwright/test';

const UVM_LESSONS = [
  { title: 'The First UVM Test', route: '/lesson/uvm/reporting' },
  { title: 'Sequence Items', route: '/lesson/uvm/seq-item' },
  { title: 'Sequences', route: '/lesson/uvm/sequence' },
  { title: 'The Driver', route: '/lesson/uvm/driver' },
  { title: 'Constrained-Random Scenarios', route: '/lesson/uvm/constrained-random' },
  { title: 'Monitor and Scoreboard', route: '/lesson/uvm/monitor' },
  { title: 'Environment and Test', route: '/lesson/uvm/env' },
  { title: 'Functional Coverage', route: '/lesson/uvm/covergroup' },
  { title: 'Cross Coverage', route: '/lesson/uvm/cross-coverage' },
  { title: 'Coverage-Driven Verification', route: '/lesson/uvm/coverage-driven' },
  { title: 'Factory Overrides', route: '/lesson/uvm/factory-override' }
];

async function goToLesson(page, lesson) {
  if (!lesson || !lesson.route) {
    throw new Error(`Invalid UVM lesson route mapping: ${JSON.stringify(lesson)}`);
  }
  await page.goto(lesson.route);
  await expect(page.getByRole('heading', { level: 2, name: lesson.title })).toBeVisible();
}

async function applySolution(page) {
  await page.getByTestId('options-button').click();
  const solveBtn = page.getByTestId('solve-button');
  if (await solveBtn.count() === 0) { await page.keyboard.press('Escape'); return; }

  const label = ((await solveBtn.textContent()) ?? '').trim();
  if (label === 'Reset to starter') {
    // Already solved — close menu and return
    await page.keyboard.press('Escape');
    return;
  }
  await solveBtn.click();
}

async function expectCleanUvmRun(logs) {
  await expect(logs).toContainText('$ circt-verilog', { timeout: 45_000 });
  await expect(logs).toContainText('--uvm-path /circt/uvm-core', { timeout: 45_000 });
  await expect.poll(
    async () => (await logs.textContent()) ?? '',
    { timeout: 45_000, intervals: [250, 500, 1000] }
  ).toMatch(/\$ circt-sim|runtime unavailable|# circt-verilog exit code: 1/);

  const text = (await logs.textContent()) ?? '';
  expect(text).toContain('$ circt-sim');
  expect(text).toContain('--mode interpret');
  expect(text).not.toContain('--compiled');
  expect(text).not.toContain('# circt-verilog exit code: 1');
  expect(text).not.toContain('# circt-sim exit code: 1');
  expect(text).not.toContain('runtime unavailable');
  expect(text).not.toContain('uvm-lite compatibility shim');
  expect(text).not.toContain("unknown package 'uvm_pkg'");
  expect(text).not.toContain("'uvm_macros.svh': No such file or directory");
  expect(text).not.toContain('Failed to load UVM manifest: 404');
  expect(text).not.toContain('not a valid top-level module');
  expect(text).not.toContain('redefinition of');
}

for (const lesson of UVM_LESSONS) {
  test(`UVM: ${lesson.title}`, async ({ page }) => {
    await goToLesson(page, lesson);
    await applySolution(page);
    await page.getByTestId('run-button').click();
    await expectCleanUvmRun(page.getByTestId('runtime-logs'));
  });
}
