/**
 * Smoke tests for a representative sample of lessons across all parts.
 * Each test applies the solution and runs it, verifying that the CIRCT
 * pipeline completes without errors.
 */
import { test, expect } from '@playwright/test';

async function goToLesson(page, chapterName, lessonName) {
  await page.goto('/');
  await page.getByRole('button', { name: chapterName }).click();
  await page.getByRole('button', { name: new RegExp(lessonName) }).click();
  await expect(page.getByRole('heading', { level: 2, name: lessonName })).toBeVisible();
}

/** Open the gear menu then click the solve/reset button inside it. */
async function clickSolve(page) {
  await page.getByTestId('options-button').click();
  await page.getByTestId('solve-button').click();
}

async function expectInterpretMode(logs) {
  await expect(logs).toContainText('--mode interpret');
  await expect(logs).not.toContainText('--compiled');
}

// ── Navigation ────────────────────────────────────────────────────────────────

test('prev/next navigate between lessons', async ({ page }) => {
  await page.goto('/');
  const h2 = page.getByTestId('lesson-title');

  await expect(h2).toHaveText('Welcome');
  await page.getByRole('button', { name: 'next' }).click();
  await expect(h2).toHaveText('Modules and Ports');
  await page.getByRole('button', { name: 'prev' }).click();
  await expect(h2).toHaveText('Welcome');
});

test('solve/reset toggles between solution and starter', async ({ page }) => {
  await page.goto('/');
  await page.getByRole('button', { name: 'next' }).click();

  // Open menu and verify initial state
  await page.getByTestId('options-button').click();
  const solveBtn = page.getByTestId('solve-button');
  await expect(solveBtn).toHaveText('Show solution');

  // Apply solution
  await solveBtn.click();

  // Reopen menu and verify reset state
  await page.getByTestId('options-button').click();
  await expect(solveBtn).toHaveText('Reset to starter');

  // Reset
  await solveBtn.click();

  // Reopen menu and verify back to solve
  await page.getByTestId('options-button').click();
  await expect(solveBtn).toHaveText('Show solution');
});

// ── SystemVerilog Basics ──────────────────────────────────────────────────────

test('Welcome: run outputs Hello World', async ({ page }) => {
  await page.goto('/');
  await page.getByTestId('run-button').click();

  const logs = page.getByTestId('runtime-logs');
  await expect(logs).toContainText('$ circt-verilog', { timeout: 120_000 });
  await expect(logs).toContainText('$ circt-sim', { timeout: 120_000 });
  await expectInterpretMode(logs);
  await expect(logs).not.toContainText('exit code: 1');
});

test('Up-Counter: solution simulates and produces a waveform', async ({ page }) => {
  await goToLesson(page, 'Sequential Logic', 'Up-Counter');

  await clickSolve(page);
  await page.getByTestId('run-button').click();

  const logs = page.getByTestId('runtime-logs');
  await expect(logs).toContainText('$ circt-verilog', { timeout: 120_000 });
  await expect(logs).toContainText('$ circt-sim', { timeout: 120_000 });
  await expectInterpretMode(logs);
  await expect(page.getByTestId('runtime-tab-waves')).toBeVisible({ timeout: 120_000 });
  await expect(logs).not.toContainText('exit code: 1');
});

test('Modules and Ports: waveform renders after solve and run', async ({ page }) => {
  // Pre-check: does Surfer boot in this Playwright environment?
  await page.goto('/surfer/index.html#dev');
  let surferCrashes = false;
  try {
    await expect(page.getByText('Sorry, Surfer crashed')).toBeVisible({ timeout: 3000 });
    surferCrashes = true;
  } catch {
    surferCrashes = false;
  }
  test.skip(surferCrashes, 'Surfer crashes in this Playwright environment (WebGL unavailable)');

  await page.goto('/');
  await page.getByRole('button', { name: 'next' }).click();
  await expect(page.getByTestId('lesson-title')).toHaveText('Modules and Ports');

  await clickSolve(page);
  await page.getByTestId('run-button').click();

  const logs = page.getByTestId('runtime-logs');
  await expect(logs).toContainText('$ circt-sim', { timeout: 120_000 });
  await expect(logs).not.toContainText('exit code: 1');

  // Waves tab must appear and clicking it must show rendered waveform data.
  await expect(page.getByTestId('runtime-tab-waves')).toBeVisible({ timeout: 120_000 });
  await page.getByTestId('runtime-tab-waves').click();

  const waveFrame = page.getByTestId('waveform-frame-wrapper');
  await expect(waveFrame).toHaveAttribute('data-wave-state', 'ready', { timeout: 30_000 });
});

// ── SystemVerilog Assertions ──────────────────────────────────────────────────

test('immediate-assert: solution passes assertions', async ({ page }) => {
  await goToLesson(page, 'Your First Formal Assertion', 'Immediate Assertions');

  await clickSolve(page);
  await page.getByTestId('verify-button').click();

  const logs = page.getByTestId('runtime-logs');
  await expect(logs).toContainText('$ circt-bmc', { timeout: 120_000 });
  await expect(logs).not.toContainText('exit code: 1');
});

test('sequence-basics: solution runs without errors', async ({ page }) => {
  await goToLesson(page, 'Your First Formal Assertion', 'Sequences and Properties');

  await clickSolve(page);
  await page.getByTestId('verify-button').click();

  const logs = page.getByTestId('runtime-logs');
  await expect(logs).toContainText('$ circt-bmc', { timeout: 120_000 });
  await expect(logs).not.toContainText('exit code: 1');
});
