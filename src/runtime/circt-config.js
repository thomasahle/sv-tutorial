export const CIRCT_FORK_REPO = 'git@github.com:thomasnormal/circt.git';

const DEFAULT_TOOLCHAIN = {
  verilog: {
    js: '/circt/circt-verilog.js',
    wasm: '/circt/circt-verilog.wasm'
  },
  sim: {
    js: '/circt/circt-sim.js',
    wasm: '/circt/circt-sim.wasm'
  },
  bmc: {
    js: '/circt/circt-bmc.js',
    wasm: '/circt/circt-bmc.wasm'
  }
};

const DEFAULT_VERILOG_ARGS = ['--resource-guard=false', '--ir-llhd', '--timescale', '1ns/1ns', '--single-unit'];
const DEFAULT_SIM_ARGS = ['--resource-guard=false'];
const DEFAULT_BMC_ARGS = [
  '--resource-guard=false',
  '-b',
  '3',
  '--module',
  '{top}',
  '--emit-smtlib',
  '-o',
  '-',
  '{input}'
];

function parseArgs(raw, fallback) {
  if (!raw) return fallback;
  try {
    const parsed = JSON.parse(raw);
    if (Array.isArray(parsed) && parsed.every((v) => typeof v === 'string')) {
      return parsed;
    }
  } catch {
    // Fallback to a simple shell-like split for convenience.
  }
  return raw
    .split(' ')
    .map((s) => s.trim())
    .filter(Boolean);
}

function pickUrlFromEnv(primary, fallback) {
  return primary || fallback;
}

export function getCirctRuntimeConfig() {
  return {
    toolchain: {
      verilog: {
        js: pickUrlFromEnv(import.meta.env.VITE_CIRCT_VERILOG_JS_URL, DEFAULT_TOOLCHAIN.verilog.js),
        wasm: pickUrlFromEnv(import.meta.env.VITE_CIRCT_VERILOG_WASM_URL, DEFAULT_TOOLCHAIN.verilog.wasm)
      },
      sim: {
        js: pickUrlFromEnv(import.meta.env.VITE_CIRCT_SIM_JS_URL, DEFAULT_TOOLCHAIN.sim.js),
        wasm: pickUrlFromEnv(import.meta.env.VITE_CIRCT_SIM_WASM_URL, DEFAULT_TOOLCHAIN.sim.wasm)
      },
      bmc: {
        js: pickUrlFromEnv(import.meta.env.VITE_CIRCT_BMC_JS_URL, DEFAULT_TOOLCHAIN.bmc.js),
        wasm: pickUrlFromEnv(import.meta.env.VITE_CIRCT_BMC_WASM_URL, DEFAULT_TOOLCHAIN.bmc.wasm)
      }
    },
    verilogArgs: parseArgs(import.meta.env.VITE_CIRCT_VERILOG_ARGS, DEFAULT_VERILOG_ARGS),
    simArgs: parseArgs(import.meta.env.VITE_CIRCT_SIM_ARGS, DEFAULT_SIM_ARGS),
    bmcArgs: parseArgs(import.meta.env.VITE_CIRCT_BMC_ARGS, DEFAULT_BMC_ARGS),
    note: import.meta.env.VITE_CIRCT_NOTE || ''
  };
}

export function getRuntimeEnvDoc() {
  return {
    VITE_CIRCT_VERILOG_JS_URL: 'circt-verilog JS artifact URL.',
    VITE_CIRCT_VERILOG_WASM_URL: 'circt-verilog WASM artifact URL.',
    VITE_CIRCT_SIM_JS_URL: 'circt-sim JS artifact URL.',
    VITE_CIRCT_SIM_WASM_URL: 'circt-sim WASM artifact URL.',
    VITE_CIRCT_BMC_JS_URL: 'circt-bmc JS artifact URL.',
    VITE_CIRCT_BMC_WASM_URL: 'circt-bmc WASM artifact URL.',
    VITE_CIRCT_VERILOG_ARGS: 'JSON array or space-separated args passed before source files.',
    VITE_CIRCT_SIM_ARGS: 'JSON array or space-separated args passed before MLIR input.',
    VITE_CIRCT_BMC_ARGS: 'JSON array or space-separated args for BMC fallback.'
  };
}
