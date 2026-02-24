/**
 * Unit tests for LEC counterexample extraction.
 *
 * These tests exercise the same C API calls that circt-adapter.js uses in the
 * browser (Z3_mk_config / Z3_mk_context / Z3_eval_smtlib2_string / Z3_del_context)
 * but run them in Node.js via the z3-solver package — the same WASM binary that
 * gets served to the browser at /z3/z3-built.js.
 *
 * The LEC lesson has:
 *   Spec: ~(a & b)          (NAND)
 *   Impl (buggy): ~a | b    (missing ~ on b)
 *   Impl (fixed): ~a | ~b   (De Morgan: equivalent to Spec)
 */

import { describe, it, expect, beforeAll } from 'vitest';
import { init } from 'z3-solver';

// ── z3 module setup ───────────────────────────────────────────────────────────

let em;

beforeAll(async () => {
  ({ em } = await init());
}, 30_000);

// Mirror the evalSmtlib function from circt-adapter.js exactly.
function evalSmtlib(smtlibText, { produceModels = false, em: emOverride = null } = {}) {
  const mod = emOverride ?? em;
  const cfg = mod.ccall('Z3_mk_config', 'number', [], []);
  if (produceModels) {
    mod.ccall('Z3_set_param_value', null, ['number', 'string', 'string'], [cfg, 'model', 'true']);
  }
  const ctx = mod.ccall('Z3_mk_context', 'number', ['number'], [cfg]);
  mod.ccall('Z3_del_config', null, ['number'], [cfg]);
  try {
    return mod.ccall('Z3_eval_smtlib2_string', 'string', ['number', 'string'], [ctx, smtlibText]);
  } finally {
    mod.ccall('Z3_del_context', null, ['number'], [ctx]);
  }
}

// Mirror the model parsing from circt-adapter.js exactly.
function parseModel(modelOut) {
  const modelFlat = (modelOut || '').replace(/\s+/g, ' ');
  const assignments = [];
  const bvRe = /\(define-fun\s+\|?(\S+?)\|?\s+\(\)\s+\(_\s+BitVec\s+\d+\)\s+(#x[0-9a-fA-F]+|#b[01]+)\s*\)/g;
  let m;
  while ((m = bvRe.exec(modelFlat)) !== null) {
    const [, name, val] = m;
    const num = val.startsWith('#x') ? parseInt(val.slice(2), 16) : parseInt(val.slice(2), 2);
    assignments.push(`${name}=${num}`);
  }
  const boolRe = /\(define-fun\s+\|?(\S+?)\|?\s+\(\)\s+Bool\s+(true|false)\s*\)/g;
  while ((m = boolRe.exec(modelFlat)) !== null) {
    assignments.push(`${m[1]}=${m[2] === 'true' ? 1 : 0}`);
  }
  return assignments;
}

// ── SMT-LIB fixtures ──────────────────────────────────────────────────────────

// Buggy Impl: ~a | b  (should be ~a | ~b)
// Distinguishing input: a=1, b=1 → Spec=0, Impl=1
const BUGGY_LEC = `
(declare-const a (_ BitVec 1))
(declare-const b (_ BitVec 1))
(assert (not (= (bvnot (bvand a b)) (bvor (bvnot a) b))))
(check-sat)
`;

// Fixed Impl: ~a | ~b  (equivalent to Spec by De Morgan)
const FIXED_LEC = `
(declare-const a (_ BitVec 1))
(declare-const b (_ BitVec 1))
(assert (not (= (bvnot (bvand a b)) (bvor (bvnot a) (bvnot b)))))
(check-sat)
`;

// ── check-sat ─────────────────────────────────────────────────────────────────

describe('check-sat', () => {
  it('returns sat for buggy Impl (circuits differ)', () => {
    expect(evalSmtlib(BUGGY_LEC).trim()).toBe('sat');
  });

  it('returns unsat for fixed Impl (circuits equivalent)', () => {
    expect(evalSmtlib(FIXED_LEC).trim()).toBe('unsat');
  });
});

// ── get-model ─────────────────────────────────────────────────────────────────

describe('get-model', () => {
  it('returns a model for the buggy Impl', () => {
    const out = evalSmtlib(BUGGY_LEC + '\n(get-model)\n', { produceModels: true });
    expect(out).toContain('sat');
    expect(out).toContain('define-fun');
  });

  it('model contains a and b assignments', () => {
    const out = evalSmtlib(BUGGY_LEC + '\n(get-model)\n', { produceModels: true });
    const assignments = parseModel(out);
    expect(assignments.length).toBeGreaterThan(0);
    // Both a and b should appear
    const vars = Object.fromEntries(assignments.map(s => s.split('=')));
    expect(vars).toHaveProperty('a');
    expect(vars).toHaveProperty('b');
  });

  it('counterexample is a valid distinguishing input for the buggy Impl', () => {
    const out = evalSmtlib(BUGGY_LEC + '\n(get-model)\n', { produceModels: true });
    const assignments = parseModel(out);
    const vars = Object.fromEntries(assignments.map(s => s.split('=')));
    const a = Number(vars.a);
    const b = Number(vars.b);
    // Verify the counterexample actually distinguishes Spec from Impl:
    //   Spec(a, b) = ~(a & b)
    //   Impl(a, b) = ~a | b   (buggy)
    const spec = (~(a & b)) & 1;
    const impl = (~a | b) & 1;
    expect(spec).not.toBe(impl);
  });

  it('two consecutive evalSmtlib calls both succeed (same instance)', () => {
    // Validates the z3 module is reusable for a second call.
    const r1 = evalSmtlib(BUGGY_LEC);
    expect(r1.trim()).toBe('sat');
    const r2 = evalSmtlib(BUGGY_LEC + '\n(get-model)\n', { produceModels: true });
    expect(r2).toContain('sat');
    expect(r2).toContain('define-fun');
  });

  it('get-model on a fresh instance works after a prior check-sat call', async () => {
    // This mirrors the browser fix: the first evalSmtlib call may corrupt the
    // module's internal exit state, so model extraction uses a fresh instance.
    const r1 = evalSmtlib(BUGGY_LEC);
    expect(r1.trim()).toBe('sat');

    const { em: freshEm } = await init();
    const r2 = evalSmtlib(BUGGY_LEC + '\n(get-model)\n', { produceModels: true, em: freshEm });
    const assignments = parseModel(r2);
    const vars = Object.fromEntries(assignments.map(s => s.split('=')));
    expect(vars).toHaveProperty('a');
    expect(vars).toHaveProperty('b');
  });
});

// ── model parsing ─────────────────────────────────────────────────────────────

describe('parseModel', () => {
  it('parses binary BitVec values', () => {
    const fakeModel = `sat
(
  (define-fun b () (_ BitVec 1)
    #b0)
  (define-fun a () (_ BitVec 1)
    #b1)
)`;
    const result = parseModel(fakeModel);
    expect(result).toContain('a=1');
    expect(result).toContain('b=0');
  });

  it('parses hex BitVec values', () => {
    const fakeModel = `sat
(
  (define-fun x () (_ BitVec 8)
    #xff)
)`;
    expect(parseModel(fakeModel)).toContain('x=255');
  });

  it('parses Bool values', () => {
    const fakeModel = `sat
( (define-fun rst () Bool true) )`;
    expect(parseModel(fakeModel)).toContain('rst=1');
  });

  it('handles quoted identifiers', () => {
    const fakeModel = `sat
( (define-fun |my.signal| () (_ BitVec 4) #xa) )`;
    expect(parseModel(fakeModel)).toContain('my.signal=10');
  });

  it('returns empty array for unsat output', () => {
    expect(parseModel('unsat')).toHaveLength(0);
  });
});
