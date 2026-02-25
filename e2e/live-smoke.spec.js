/**
 * Smoke tests against the live GitHub Pages deployment at
 * https://thomasnormal.github.io/sv-tutorial/
 *
 * These tests mirror the solutions.spec.js logic but navigate directly
 * to the deployed URL (no local build required).
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
  await page.getByRole('button', { name: chapterName }).click();
  await page.getByRole('button', { name: lessonName }).click();
  await expect(page.getByRole('heading', { level: 2, name: lessonName })).toBeVisible();
}

const COMPILE_TIMEOUT = 90_000;
const Z3_TIMEOUT      = 120_000;

// ── Smoke tests ───────────────────────────────────────────────────────────────

test('[app] loads and shows lesson navigation', async ({ page }) => {
  await page.goto(BASE);
  // The app should load and show at least one chapter button
  await expect(page.getByRole('button', { name: 'Introduction' })).toBeVisible({ timeout: 30_000 });
});

test('[sim] Welcome — run button produces output, no compile error', async ({ page }) => {
  await goToLesson(page, 'Introduction', 'Welcome');
  await page.getByTestId('options-button').click();
  await page.getByTestId('solve-button').click();
  await page.getByTestId('run-button').click();
  const logs = page.getByTestId('runtime-logs');
  await expect(logs).not.toContainText('# circt-verilog exit code: 1', { timeout: COMPILE_TIMEOUT });
});

test('[sim] Concurrent Assertions — runtime assertions chapter visible, assertionFail produced', async ({ page }) => {
  await goToLesson(page, 'Runtime Assertions', 'Concurrent Assertions in Simulation');
  await page.getByTestId('options-button').click();
  await page.getByTestId('solve-button').click();
  await page.getByTestId('run-button').click();
  const logs = page.getByTestId('runtime-logs');
  await expect(logs).not.toContainText('# circt-verilog exit code: 1', { timeout: COMPILE_TIMEOUT });
  await expect(logs).toContainText('SVA assertion failed', { timeout: COMPILE_TIMEOUT });
});

test('[bmc] Immediate Assertions — verify runs z3', async ({ page }) => {
  await goToLesson(page, 'Your First Formal Assertion', 'Immediate Assertions');
  await page.getByTestId('options-button').click();
  await page.getByTestId('solve-button').click();
  await page.getByTestId('verify-button').click();
  const logs = page.getByTestId('runtime-logs');
  await expect(logs).not.toContainText('# circt-verilog exit code: 1', { timeout: COMPILE_TIMEOUT });
  await expect(logs).not.toContainText('# circt-bmc exit code: 1', { timeout: COMPILE_TIMEOUT });
  await expect(logs).toContainText('[z3]', { timeout: Z3_TIMEOUT });
});

test('[bmc] Implication — verify runs z3', async ({ page }) => {
  await goToLesson(page, 'Implication & BMC', 'Implication: |-> and |=>');
  await page.getByTestId('options-button').click();
  await page.getByTestId('solve-button').click();
  await page.getByTestId('verify-button').click();
  const logs = page.getByTestId('runtime-logs');
  await expect(logs).not.toContainText('# circt-verilog exit code: 1', { timeout: COMPILE_TIMEOUT });
  await expect(logs).not.toContainText('# circt-bmc exit code: 1', { timeout: COMPILE_TIMEOUT });
  await expect(logs).toContainText('[z3]', { timeout: Z3_TIMEOUT });
});

test('[lec] Logical Equivalence Checking — z3 proves unsat', async ({ page }) => {
  await goToLesson(page, 'Formal Verification', 'Logical Equivalence Checking');
  await page.getByTestId('options-button').click();
  await page.getByTestId('solve-button').click();
  await page.getByTestId('verify-button').click();
  const logs = page.getByTestId('runtime-logs');
  await expect(logs).not.toContainText('# circt-verilog exit code: 1', { timeout: COMPILE_TIMEOUT });
  await expect(logs).not.toContainText('# circt-lec exit code: 1', { timeout: COMPILE_TIMEOUT });
  await expect(logs).toContainText('[z3] unsat', { timeout: Z3_TIMEOUT });
});
