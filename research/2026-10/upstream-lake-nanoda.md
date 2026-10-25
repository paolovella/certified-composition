# Draft upstream issue: `lake check --paranoid` runs nanoda with 4 threads, which overflow

Status: **draft, not filed.** Filing is the user's call (P0-02 Log, 2026-10-25). Evidence is in
`tools/receipts/p002-nanoda-*` and `p002-lakecheck-root`.

---

**Title:** `lake check --paranoid`: nanoda overflows its stack on a medium export, because Lake
hardcodes `num_threads: 4` and clears the environment

**Version:** Lean `v4.35.0` (Lake and the `nanoda_bin` bundled with that toolchain), Linux x86_64.

**What happens.** `lake check --paranoid` on a package of about 66,700 declarations (two
mathlib-free libraries) gets "accepted" from leanchecker, leanchecker-paranoid, lean4lean,
con-leche and con-ron. nanoda aborts:

```
thread 'thread_2' (…) has overflowed its stack
fatal runtime error: stack overflow, aborting
```

So the check fails, and the user can't do anything about it from outside.

**Why it can't be worked around.** `runExternalKernel` in `src/lake/Lake/CLI/Check.lean` writes
the nanoda config with `("num_threads", 4)`, and it spawns every external kernel with
`envPass := #["LEAN_ABORT_ON_PANIC"]`. No setting reaches nanoda.

**Measured, running `nanoda_bin` by hand on the same export:**

| threads | environment | result |
|---|---|---|
| 4 | none | overflow (`thread_0`) |
| 4 | `RUST_MIN_STACK=1073741824` | overflow (`thread_2`) |
| 4 | `ulimit -s unlimited` + `RUST_MIN_STACK=1073741824` | overflow (`thread_2`) |
| 1 | none | overflow (`main`) |
| 1 | `ulimit -s unlimited` | **accepts**, 66660 declarations, 63 s |

With 4 threads the worker stacks overflow whatever the environment says. With 1 thread nanoda
works on the main thread, and that thread's stack follows `ulimit -s`. Even so, the 1-thread
default needs a larger stack than the usual 8 MiB.

**Suggested fixes (any one would do):**
1. Make `num_threads` configurable (a `lake check` flag or lakefile option), or default it to 1.
2. Have nanoda give its worker threads a stack size that is large or configurable, for example
   with `std::thread::Builder::stack_size`. (This may belong in nanoda's own tracker.)
3. Let `lake check` pass a chosen set of variables, for example `RUST_MIN_STACK`, through to the
   sandboxed kernels. This helps only if nanoda's threads actually honour it.

**Repro outline.** Use any package that is large enough. `lake check --paranoid` from its root
fails on nanoda. Then run `lake env leanexport <Root> > x.ndjson` and give `nanoda_bin` a config
with `num_threads` 4, then 1, as in the table above.
