#!/usr/bin/env bash
# shellcheck shell=bash

# Pinned external toolchain/repository versions for reproducible builds.

readonly NODE_MAJOR_VERSION_LOCKED="22"
readonly EMSDK_VERSION_LOCKED="4.0.21"

readonly CIRCT_REPO_LOCKED="https://github.com/thomasnormal/circt.git"
readonly CIRCT_REF_LOCKED="df651da4a788094d4610b0bbae59d935b26eb36d"
readonly CIRCT_LLVM_SUBMODULE_REF_LOCKED="aa3d6b37c7945bfb4c261dd994689de2a2de25bf"

readonly SURFER_ARTIFACT_URL_LOCKED="https://gitlab.com/surfer-project/surfer/-/jobs/artifacts/main/download?job=pages_build"
readonly SURFER_ARTIFACT_SHA256_LOCKED="2a684122436e7a7729cc4e57062fdc2ce8ec5fa096d84ca383dd59011012b873"
