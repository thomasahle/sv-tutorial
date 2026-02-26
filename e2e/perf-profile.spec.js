// Temporary performance profiling spec — not meant for CI assertions.
// Run with: npx playwright test e2e/perf-profile.spec.js --reporter=list

import { test } from '@playwright/test';

const BASE_URL = 'http://127.0.0.1:4173';

test('Core Web Vitals on /lesson/sv/welcome', async ({ page }) => {
  // Inject PerformanceObserver listeners before navigation so we catch all entries.
  await page.addInitScript(() => {
    window.__cwv = { lcp: null, fcp: null, cls: 0, inp: null };

    // LCP
    try {
      new PerformanceObserver((list) => {
        const entries = list.getEntries();
        if (entries.length) {
          window.__cwv.lcp = entries[entries.length - 1].startTime;
        }
      }).observe({ type: 'largest-contentful-paint', buffered: true });
    } catch (e) {}

    // FCP
    try {
      new PerformanceObserver((list) => {
        for (const entry of list.getEntries()) {
          if (entry.name === 'first-contentful-paint') {
            window.__cwv.fcp = entry.startTime;
          }
        }
      }).observe({ type: 'paint', buffered: true });
    } catch (e) {}

    // CLS
    try {
      new PerformanceObserver((list) => {
        for (const entry of list.getEntries()) {
          if (!entry.hadRecentInput) {
            window.__cwv.cls += entry.value;
          }
        }
      }).observe({ type: 'layout-shift', buffered: true });
    } catch (e) {}

    // INP (Interaction to Next Paint) — only available in some browsers
    try {
      new PerformanceObserver((list) => {
        for (const entry of list.getEntries()) {
          if (window.__cwv.inp === null || entry.duration > window.__cwv.inp) {
            window.__cwv.inp = entry.duration;
          }
        }
      }).observe({ type: 'event', buffered: true, durationThreshold: 16 });
    } catch (e) {}
  });

  const navStart = Date.now();
  await page.goto(`${BASE_URL}/lesson/sv/welcome`, { waitUntil: 'networkidle' });
  const navEnd = Date.now();

  // Give observers a moment to flush
  await page.waitForTimeout(1000);

  const cwv = await page.evaluate(() => window.__cwv);

  // TTFB from Navigation Timing API
  const ttfb = await page.evaluate(() => {
    const nav = performance.getEntriesByType('navigation')[0];
    return nav ? nav.responseStart - nav.requestStart : null;
  });

  console.log('\n========== CORE WEB VITALS ==========');
  console.log(`TTFB:  ${ttfb !== null ? ttfb.toFixed(1) + ' ms' : 'n/a'}`);
  console.log(`FCP:   ${cwv.fcp !== null ? cwv.fcp.toFixed(1) + ' ms' : 'n/a'}`);
  console.log(`LCP:   ${cwv.lcp !== null ? cwv.lcp.toFixed(1) + ' ms' : 'n/a'}`);
  console.log(`CLS:   ${cwv.cls.toFixed(4)}`);
  console.log(`INP:   ${cwv.inp !== null ? cwv.inp.toFixed(1) + ' ms' : 'n/a (no interactions)'}`);
  console.log(`Wall-clock page load: ${navEnd - navStart} ms`);
  console.log('=====================================\n');
});

test('JS resource load times on /lesson/sv/welcome', async ({ page }) => {
  await page.goto(`${BASE_URL}/lesson/sv/welcome`, { waitUntil: 'networkidle' });
  await page.waitForTimeout(500);

  const resources = await page.evaluate(() => {
    return performance.getEntriesByType('resource')
      .filter(r => r.initiatorType === 'script' || r.name.endsWith('.js') || r.name.endsWith('.wasm'))
      .map(r => ({
        name: r.name.replace(/.*\//, '').slice(0, 60),
        duration: r.duration,
        transferSize: r.transferSize,
        encodedBodySize: r.encodedBodySize,
        decodedBodySize: r.decodedBodySize,
        initiatorType: r.initiatorType,
      }))
      .sort((a, b) => b.duration - a.duration);
  });

  const totalTransfer = await page.evaluate(() => {
    return performance.getEntriesByType('resource')
      .reduce((sum, r) => sum + (r.transferSize || 0), 0);
  });

  const totalDecoded = await page.evaluate(() => {
    return performance.getEntriesByType('resource')
      .reduce((sum, r) => sum + (r.decodedBodySize || 0), 0);
  });

  console.log('\n========== JS/WASM RESOURCE LOAD TIMES (slowest first) ==========');
  for (const r of resources.slice(0, 20)) {
    const kb = r.transferSize ? (r.transferSize / 1024).toFixed(1) + ' KB' : '(cached/0)';
    console.log(`  ${r.duration.toFixed(0).padStart(6)} ms  ${kb.padStart(12)}  ${r.name}`);
  }
  console.log(`\nTotal JS/WASM resources shown: ${resources.length}`);
  console.log(`Total transferred (all resources): ${(totalTransfer / 1024).toFixed(1)} KB`);
  console.log(`Total decoded (all resources):     ${(totalDecoded / 1024).toFixed(1)} KB`);
  console.log('==================================================================\n');
});

test('SPA navigation timing: welcome → modules-and-ports → always-comb', async ({ page }) => {
  // The sidebar uses button[data-active] for lesson buttons, not <a> links.
  // Chapter buttons have no data-active attribute.
  await page.goto(`${BASE_URL}/lesson/sv/welcome`, { waitUntil: 'networkidle' });

  // Wait for sidebar to initialise
  await page.locator('button[data-active]').first().waitFor({ timeout: 10000 });

  // --- Navigate to modules-and-ports ---
  // "Modules and Ports" is in the "Basics" chapter.
  // First ensure the lesson button is visible; if not, open the chapter.
  const modulesBtn = page.locator('button[data-active]').filter({ hasText: 'Modules and Ports' });
  if ((await modulesBtn.count()) === 0) {
    await page.locator('button:not([data-active])').filter({ hasText: 'Basics' }).click();
  }

  const t0 = Date.now();
  await modulesBtn.first().click({ timeout: 10000 });
  // Wait for lesson content heading to appear
  await page.locator('button[data-active]').filter({ hasText: 'Modules and Ports' }).waitFor({ timeout: 10000 });
  const t1 = Date.now();
  const nav1 = t1 - t0;

  await page.waitForTimeout(300);

  // --- Navigate to always-comb ---
  // "always_comb and case" lesson name
  const alwaysBtn = page.locator('button[data-active]').filter({ hasText: 'always_comb' });
  if ((await alwaysBtn.count()) === 0) {
    // It may be in a chapter that's not yet open — try "Combinational Logic" chapter
    await page.locator('button:not([data-active])').filter({ hasText: 'Combinational Logic' }).first().click();
  }

  const t2 = Date.now();
  await alwaysBtn.first().click({ timeout: 10000 });
  await page.locator('button[data-active]').filter({ hasText: 'always_comb' }).waitFor({ timeout: 10000 });
  const t3 = Date.now();
  const nav2 = t3 - t2;

  console.log('\n========== SPA NAVIGATION TIMING ==========');
  console.log(`welcome → modules-and-ports: ${nav1} ms`);
  console.log(`modules-and-ports → always-comb: ${nav2} ms`);
  console.log(`Average SPA nav time: ${((nav1 + nav2) / 2).toFixed(0)} ms`);
  console.log('===========================================\n');
});

test('Total JS transferred summary', async ({ page }) => {
  await page.goto(`${BASE_URL}/lesson/sv/welcome`, { waitUntil: 'networkidle' });
  await page.waitForTimeout(500);

  const summary = await page.evaluate(() => {
    const entries = performance.getEntriesByType('resource');
    const byType = {};
    let totalTransfer = 0;
    let totalDecoded = 0;
    for (const r of entries) {
      const type = r.initiatorType || 'other';
      if (!byType[type]) byType[type] = { count: 0, transfer: 0, decoded: 0 };
      byType[type].count++;
      byType[type].transfer += r.transferSize || 0;
      byType[type].decoded += r.decodedBodySize || 0;
      totalTransfer += r.transferSize || 0;
      totalDecoded += r.decodedBodySize || 0;
    }
    return { byType, totalTransfer, totalDecoded, count: entries.length };
  });

  console.log('\n========== TOTAL JS TRANSFERRED ==========');
  console.log(`Total resources: ${summary.count}`);
  console.log(`Total transferred: ${(summary.totalTransfer / 1024).toFixed(1)} KB`);
  console.log(`Total decoded:     ${(summary.totalDecoded / 1024).toFixed(1)} KB`);
  console.log('\nBy initiator type:');
  for (const [type, data] of Object.entries(summary.byType).sort((a, b) => b[1].transfer - a[1].transfer)) {
    console.log(`  ${type.padEnd(12)} count=${data.count}  transfer=${(data.transfer/1024).toFixed(1)} KB  decoded=${(data.decoded/1024).toFixed(1)} KB`);
  }
  console.log('==========================================\n');
});
