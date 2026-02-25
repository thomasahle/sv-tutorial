import { test, expect } from '@playwright/test';

test.describe('offline bundle', () => {
  test('download button shows progress and ends in ready state', async ({ page }) => {
    test.setTimeout(300_000);

    await page.goto('/');
    await page.evaluate(async () => {
      for (const key of Object.keys(localStorage)) {
        if (key.startsWith('svt:')) localStorage.removeItem(key);
      }
      if ('caches' in window) {
        const keys = await caches.keys();
        await Promise.all(keys.map((key) => caches.delete(key)));
      }
      if ('serviceWorker' in navigator) {
        const regs = await navigator.serviceWorker.getRegistrations();
        await Promise.all(regs.map((reg) => reg.unregister()));
      }
    });

    await page.reload({ waitUntil: 'networkidle' });

    const offlineButton = page.getByTestId('offline-download-button');
    await expect(offlineButton).toBeVisible();

    await offlineButton.click();

    const statusChip = page.getByTestId('offline-download-status');
    await expect(statusChip).toBeVisible({ timeout: 20_000 });
    await expect(statusChip).toContainText(/^\d+\/(\d+|\?)$/, { timeout: 20_000 });
    await expect(statusChip).toContainText(/offline ready/i, { timeout: 240_000 });

    await expect(offlineButton).toHaveAttribute('aria-label', /offline bundle ready/i, { timeout: 240_000 });

    const readyState = await page.evaluate(async () => {
      const state = localStorage.getItem('svt:offline-ready-v1');
      if (state !== 'ready' || !('caches' in window)) return false;
      const cache = await caches.open('svt-runtime-v1');
      const keys = await cache.keys();
      return keys.some((req) => req.url.includes('/__offline__/ready'));
    });

    expect(readyState).toBe(true);
  });
});
