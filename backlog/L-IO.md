---
id: L-IO
title: "Named sinks and the monitor's events on the machine: emit to more than one sink, and check, read and release as events of rvLang, compared with QEMU"
ring: 1
tier: G-X
milestone: M3 (2027-01-08)
deps: [RC-03]
closes: ['VULN-COVERAGE §3.0: rows 3, 4, 7 and 14 observe Ev.check, Ev.read, Ev.release and Ev.emit at named sinks, and the machine produces only Ev.emit "out"']
acceptance: a run of rvLang produces Ev.emit at two sinks or more and Ev.check, Ev.read and Ev.release; the source language has a command for each, carried by both passes with no kernel change; QEMU agrees with the model on each new behaviour, with a broken model for each; every existing literal image is byte-for-byte unchanged, and every existing certificate still transfers
kill: if an event cannot be produced without a change to Kernel/Obs.lean, or the passes' cover and low_cover fail on the new commands, stop and report
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track A, 2026-11-30 to 2026-12-11. Every row that is not about secrets or cost observes an event the machine cannot yet produce. This item adds the events and no certificate.

Today `sysWriteStep` (`Slice/Rv.lean`) accepts descriptor 1 only and produces `Ev.emit "out"`. Any other descriptor faults.

1. **A design note first**, `research/2026-11/L-IO-DESIGN.md`, which settles three things before any Lean:
   - which descriptors are sinks, and their names (the starting proposal: 1 `out`, 2 `log`, and one each for `sql` and `fs`);
   - how `check r`, `read r` and `release tag` appear on a real machine. The starting proposal is a fixed record written to a monitor descriptor, which the model reads as `Ev.check`, `Ev.read` or `Ev.release`. Then QEMU's run shows each event in a file, and the comparison is byte for byte;
   - where a resource's bytes come from. The starting proposal is a stated region of the input, with `read r` marking the access, as `UCmd` does.
   The note states the trust assumption: the monitor reads its descriptor, and is an oracle.
2. **The machine.** The model accepts the stated descriptors and maps each to its event. QEMU comparison in `rv_diff.py`, and a broken model for each: a wrong sink, a dropped event, a record one byte short.
3. **The language.** `emitTo sink`, `check r`, `read r` and `release tag` in `Slice2/Source.lean`, through `Slots.lean` and `Lower.lean`. Mutants in `slice2_low_mut.py`.
4. **The C reading.** How the front end reads a call to a stated monitor function, in a READING note, tested against clang.
5. **Unchanged:** the seven literal images and their QEMU comparisons, rerun.

## Log
