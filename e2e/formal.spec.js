import { test, expect } from '@playwright/test';

// Helper: expand a chapter in the sidebar and click a lesson.
// Lesson buttons carry data-active; chapter buttons do not — this distinction
// prevents strict-mode violations from partial name matches.
async function goToLesson(page, chapterName, lessonName) {
  await page.goto('/');
  const lessonBtn = page.locator('button[data-active]').filter({ hasText: lessonName });
  if ((await lessonBtn.count()) === 0) {
    await page.locator('button:not([data-active])').filter({ hasText: chapterName }).click();
  }
  await lessonBtn.click();
  await expect(page.getByRole('heading', { level: 2, name: lessonName })).toBeVisible();
}

// ── BMC: Bounded Model Checking ───────────────────────────────────────────────

test('BMC: starter code has no assertion → verify does not prove anything', async ({ page }) => {
  await goToLesson(page, 'Implication & BMC', 'Bounded Model Checking');

  await page.getByTestId('verify-button').click();

  const logs = page.getByTestId('runtime-logs');
  await expect(logs).toContainText('$ circt-verilog', { timeout: 120_000 });
  await expect(logs).toContainText('$ circt-bmc', { timeout: 120_000 });
  // No assertion in the module → bmc may exit with 0 but won't say "proved"
  await expect(logs).not.toContainText('# circt-verilog exit code: 1');
});

test('BMC: solution proves all properties within the bound', async ({ page }) => {
  await goToLesson(page, 'Implication & BMC', 'Bounded Model Checking');

  await page.getByTestId('solve-button').click();
  await page.getByTestId('verify-button').click();

  const logs = page.getByTestId('runtime-logs');
  await expect(logs).toContainText('$ circt-verilog', { timeout: 120_000 });
  await expect(logs).toContainText('$ circt-bmc', { timeout: 120_000 });
  await expect(logs).toContainText('[z3] unsat', { timeout: 120_000 });
  await expect(logs).not.toContainText('# circt-verilog exit code: 1');
  await expect(logs).not.toContainText('# circt-bmc exit code: 1');
});

test('BMC: shows only verify button, no run button', async ({ page }) => {
  await goToLesson(page, 'Implication & BMC', 'Bounded Model Checking');

  await expect(page.getByTestId('verify-button')).toBeVisible();
  await expect(page.getByTestId('run-button')).toHaveCount(0);
});

// ── BMC: assume property ──────────────────────────────────────────────────────

test('assume property: solution proves property with constraint', async ({ page }) => {
  await goToLesson(page, 'Formal Verification', 'assume property');

  await page.getByTestId('solve-button').click();
  await page.getByTestId('verify-button').click();

  const logs = page.getByTestId('runtime-logs');
  await expect(logs).toContainText('[z3] unsat', { timeout: 120_000 });
});

// ── LEC: Logical Equivalence Checking ────────────────────────────────────────

test('LEC: only shows verify (LEC) button, no run button', async ({ page }) => {
  await goToLesson(page, 'Formal Verification', 'Logical Equivalence Checking');

  await expect(page.getByTestId('verify-button')).toBeVisible();
  await expect(page.getByTestId('verify-button')).toHaveText('verify (LEC)');
  await expect(page.getByTestId('run-button')).toHaveCount(0);
});

test('LEC: buggy Impl is detected as NOT equivalent', async ({ page }) => {
  await goToLesson(page, 'Formal Verification', 'Logical Equivalence Checking');

  await page.getByTestId('verify-button').click();

  const logs = page.getByTestId('runtime-logs');
  await expect(logs).toContainText('$ circt-verilog', { timeout: 120_000 });
  await expect(logs).toContainText('$ circt-lec', { timeout: 120_000 });
  await expect(logs).toContainText('[z3] sat', { timeout: 120_000 });
  await expect(logs).not.toContainText('# circt-verilog exit code: 1');
});

test('LEC: fixed Impl is proved equivalent to Spec', async ({ page }) => {
  await goToLesson(page, 'Formal Verification', 'Logical Equivalence Checking');

  await page.getByTestId('solve-button').click();
  await page.getByTestId('verify-button').click();

  const logs = page.getByTestId('runtime-logs');
  await expect(logs).toContainText('[z3] unsat', { timeout: 120_000 });
  await expect(logs).not.toContainText('# circt-verilog exit code: 1');
  await expect(logs).not.toContainText('# circt-lec exit code: 1');
});
