#!/usr/bin/env bash
# shellcheck shell=bash

# Pinned external toolchain/repository versions for reproducible builds.

readonly NODE_MAJOR_VERSION_LOCKED="22"
readonly EMSDK_VERSION_LOCKED="4.0.21"

readonly CIRCT_REPO_LOCKED="https://github.com/thomasnormal/circt.git"
readonly CIRCT_REF_LOCKED="6b1f2e8b799352ff3dce2d1ebc6f3eb8f2e360c7"
readonly CIRCT_LLVM_SUBMODULE_REF_LOCKED="972cd847efb20661ea7ee8982dd19730aa040c75"

readonly SURFER_ARTIFACT_URL_LOCKED="https://gitlab.com/surfer-project/surfer/-/jobs/artifacts/main/download?job=pages_build"
readonly SURFER_ARTIFACT_SHA256_LOCKED="17b163a919177f2f573bfe3b0021b7328c64908e35a643980b5b06cb1b08469a"
