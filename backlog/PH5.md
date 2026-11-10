---
id: PH5
title: Phase 5 bytes: encoder, ELF, kernel-evaluated pipeline, NDJSON extraction, QEMU/Spike differential
ring: 1
tier: G-X
deps: [PH4, S-SAIL]
closes: ['no runnable certified artifact']
acceptance: first Artifact with binary_carries and attestation; binary runs and matches
kill: kernel compile over 30 min for 500 nodes: per-function modules + validation
status: planned
---

## Plan

See PLAN-2026-10.md. Write the concrete steps here before starting work.

## Log
- 2026-11-10, **most of this item has landed under other names, and it stays open only for what has not** ([`PLAN-2026-11`](../PLAN-2026-11.md) §6).
  - Landed: the encoder and the ELF (`VS-1`), the pipeline evaluated in the kernel (`VS-1`, `VS-2`), the differential against QEMU (`rv_diff.py`, from `VS-1` on).
  - Not done, and parked past 1.0: the Sail link (`S-SAIL`), a second emulator, NDJSON extraction.
  - Its dependency on `PH4` no longer describes anything: the bytes came without the optimising passes.
