# AGENT

## Engineering Priority

- Prioritize long-term maintainability over short-term patching.
- Prefer real/root-cause fixes over narrow or temporary workarounds.
- If a quick workaround is used to unblock progress, follow up with the durable fix in the same change whenever feasible.

## Resource Safety

- Treat `ninja`, `circt-sim`, large link steps, and similarly heavy tools as high-risk for local system stability.
- Always run heavy commands with explicit resource limits (for example: CPU parallelism limits, memory caps, and wall-clock timeouts).
- Prefer incremental/targeted builds over whole-tree builds when possible.
- Avoid running multiple heavy builds concurrently.
- If resource limits are unclear, choose conservative defaults first and scale up only when needed.
