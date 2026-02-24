/**
 * E2E tests for the cocotb runner (circt-verilog → circt-sim + Pyodide).
 */
import { test, expect } from '@playwright/test';

async function goToLesson(page, lessonName) {
  await page.goto('/');
  await page.getByRole('button', { name: 'cocotb Basics' }).click();
  await page.getByRole('button', { name: new RegExp(lessonName) }).click();
  await expect(page.getByRole('heading', { level: 2, name: lessonName })).toBeVisible();
}

test('cocotb: shows "test" button, not "run"', async ({ page }) => {
  await goToLesson(page, 'Your First cocotb Test');
  await expect(page.getByTestId('run-button')).toHaveText('test');
});

test('cocotb: Your First cocotb Test — solution passes all assertions', async ({ page }) => {
  await goToLesson(page, 'Your First cocotb Test');

  // The Python test file is the starter; apply the SV solution (correct adder).
  await page.getByTestId('solve-button').click();
  await page.getByTestId('run-button').click();

  const logs = page.getByTestId('runtime-logs');
  // Pyodide download can be slow on first run — generous timeout.
  await expect(logs).toContainText('[cocotb] Simulation complete', { timeout: 180_000 });
  await expect(logs).not.toContainText('[cocotb] Python error');
  await expect(logs).not.toContainText('# cocotb error');
  await expect(logs).not.toContainText('AssertionError');
});

test('cocotb: Clock and Timing — solution passes all assertions', async ({ page }) => {
  await goToLesson(page, 'Clock and Timing');

  await page.getByTestId('solve-button').click();
  await page.getByTestId('run-button').click();

  const logs = page.getByTestId('runtime-logs');
  await expect(logs).toContainText('[cocotb] Simulation complete', { timeout: 180_000 });
  await expect(logs).not.toContainText('[cocotb] Python error');
  await expect(logs).not.toContainText('AssertionError');
});
