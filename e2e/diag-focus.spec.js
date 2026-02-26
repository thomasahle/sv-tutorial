/**
 * Diagnostic: probe Surfer's id_of_name / FocusItem / VisibleItemIndex in the current build.
 * Run with: npx playwright test e2e/diag-focus.spec.js --headed
 */
import { test, expect } from '@playwright/test';

test('diag: probe FocusItem vs id_of_name in current Surfer build', async ({ page }) => {
  // Skip if Surfer crashes (no WebGL)
  await page.goto('/surfer/index.html#dev');
  try {
    await expect(page.getByText('Sorry, Surfer crashed')).toBeVisible({ timeout: 3000 });
    test.skip(true, 'Surfer crashes in this environment');
  } catch { /* good — Surfer works */ }

  // Use priority-enc which has a simple flat scope (grant/req/valid signals)
  // and is known to generate a VCD waveform from the solution.
  await page.goto('/lesson/sv/priority-enc');
  await page.evaluate(() => {
    for (const key of Object.keys(localStorage)) {
      if (key.startsWith('svt:')) localStorage.removeItem(key);
    }
  });
  await page.getByTitle('Editor options').click();
  await page.getByTestId('solve-button').click();
  await page.getByTestId('run-button').click();
  await expect(page.getByTestId('runtime-tab-waves')).toBeVisible({ timeout: 90_000 });
  await page.getByTestId('runtime-tab-waves').click();

  const waveFrame = page.getByTestId('waveform-frame-wrapper');
  await expect(waveFrame).toHaveAttribute('data-wave-state', 'ready', { timeout: 30_000 });

  // Give Surfer extra time after signals are ready
  await page.waitForTimeout(1000);

  const iframeHandle = await page.getByTestId('waveform-iframe').elementHandle();
  const iframeCtx = await iframeHandle.contentFrame();

  const result = await iframeCtx.evaluate(async () => {
    const cw = window;
    const out = {};

    // 1. Which APIs exist?
    out.apis = {
      id_of_name:          typeof cw.id_of_name,
      index_of_name:       typeof cw.index_of_name,
      focused_item:        typeof cw.focused_item,
      get_focused_item:    typeof cw.get_focused_item,
      visible_item_count:  typeof cw.visible_item_count,
      item_at_index:       typeof cw.item_at_index,
      name_of_id:          typeof cw.name_of_id,
    };

    // 1b. index_of_name for the same paths (should return VisibleItemIndex, different from id_of_name)
    if (typeof cw.index_of_name === 'function') {
      const paths2 = ['tb.grant', 'tb.req', 'tb.valid', 'grant', 'req', 'valid', 'tb'];
      out.index_of_name = {};
      for (const p of paths2) {
        try { out.index_of_name[p] = await cw.index_of_name(p); } catch (e) { out.index_of_name[p] = 'ERR:' + e.message; }
      }
    }

    // 2. id_of_name for various paths (priority-enc signals: grant, req, valid)
    if (typeof cw.id_of_name === 'function') {
      const paths = ['tb.grant', 'tb.req', 'tb.valid', 'grant', 'req', 'valid', 'tb'];
      out.id_of_name = {};
      for (const p of paths) {
        try { out.id_of_name[p] = await cw.id_of_name(p); } catch (e) { out.id_of_name[p] = 'ERR:' + e.message; }
      }
    }

    // 3. Try focused_item / get_focused_item
    if (typeof cw.focused_item === 'function') {
      try { out.focused_item_result = await cw.focused_item(); } catch (e) { out.focused_item_result = 'ERR:' + e.message; }
    }
    if (typeof cw.get_focused_item === 'function') {
      try { out.get_focused_item_result = await cw.get_focused_item(); } catch (e) { out.get_focused_item_result = 'ERR:' + e.message; }
    }

    // 4. Scan item_at_index(0..9) to map VisibleItemIndex → DisplayedItemRef
    if (typeof cw.visible_item_count === 'function') {
      try { out.visible_item_count = await cw.visible_item_count(); } catch (e) { out.visible_item_count = 'ERR:' + e.message; }
    }
    if (typeof cw.item_at_index === 'function') {
      out.item_at_index = {};
      for (let i = 0; i < 10; i++) {
        try { out.item_at_index[i] = await cw.item_at_index(i); } catch (e) { out.item_at_index[i] = 'ERR:' + e.message; }
      }
    }
    if (typeof cw.name_of_id === 'function') {
      out.name_of_id = {};
      for (let i = 0; i < 10; i++) {
        try { out.name_of_id[i] = await cw.name_of_id(i); } catch (e) { out.name_of_id[i] = 'ERR:' + e.message; }
      }
    }

    return out;
  });

  console.log('\n=== SURFER PROBE ===\n', JSON.stringify(result, null, 2));

  // 4. Now send FocusItem with the id_of_name value and check if focus moved
  const mainCtx = page;
  const sendMsg = async (msg) => {
    await iframeCtx.evaluate((m) => {
      window.postMessage({ command: 'InjectMessage', message: JSON.stringify(m) }, '*');
    }, msg);
    await page.waitForTimeout(300);
  };

  // Try focusing each visible item index 0..5 and after each, read focused_item
  if (result.apis.focused_item === 'function' || result.apis.get_focused_item === 'function') {
    const focusResults = {};
    for (let i = 0; i <= 5; i++) {
      await sendMsg({ FocusItem: i });
      const fi = await iframeCtx.evaluate(async () => {
        const cw = window;
        if (typeof cw.focused_item === 'function') return await cw.focused_item();
        if (typeof cw.get_focused_item === 'function') return await cw.get_focused_item();
        return null;
      });
      focusResults[`FocusItem(${i})`] = fi;
    }
    console.log('\n=== FocusItem scan ===\n', JSON.stringify(focusResults, null, 2));
  }

  // 5. After focusing what we think is cmd, send transition_next and see if cursor moves
  // Try with the id_of_name value
  // Use index_of_name (VisibleItemIndex) for FocusItem, not id_of_name (DisplayedItemRef).
  const cmdId = result.index_of_name?.['tb.req'] ?? result.id_of_name?.['tb.req'];
  if (cmdId !== undefined) {
    await sendMsg({ FocusItem: cmdId });
    await page.waitForTimeout(300);

    // Send transition_next via command file
    const cmdUrl = await mainCtx.evaluate(() => {
      const blob = new Blob(['transition_next\n'], { type: 'text/plain' });
      return URL.createObjectURL(blob);
    });
    await iframeCtx.evaluate((url) => {
      window.postMessage({ command: 'InjectMessage', message: JSON.stringify({ LoadCommandFileFromUrl: url }) }, '*');
    }, cmdUrl);
    await page.waitForTimeout(500);
    console.log(`\nSent FocusItem(${cmdId}) then transition_next`);
  }

  // Always pass — this is a diagnostic
  expect(result.apis.id_of_name).toBe('function');
});
