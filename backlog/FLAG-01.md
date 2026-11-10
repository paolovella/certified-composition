---
id: FLAG-01
title: "The flagship: one C request handler certified on every row, down to an ELF that runs, with a broken variant for each row"
ring: 2
tier: G-C
milestone: M7 (2027-03-26)
deps: [UNI-01, SEAM-01, HEAP-03]
closes: ['PLAN-2026-11 §2 point 3: 1.0''s acceptance test']
acceptance: one C file read by the front end; lcheck accepts it; the one theorem gives every row on its literal image; the ELF under QEMU agrees with the model and with clang's build on 400 requests or more, among them attack strings; for each row a variant that differs by a few lines, is refused by that row's checker, and whose image misbehaves under QEMU or in the speculating model; the kernel time and the image size, measured
kill: if the whole handler costs more than 30 minutes of kernel time, split it at a seam by SEAM-01 and record the cost
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track B then both, 2027-03-15 to 2027-03-26.

**The handler is written first, in C, by 2026-12-04**, as `research/2026-11/flagship/handler.c`, before the rows exist on the slice. It is the target each row item is tested against, and writing it early is what tells a row item that its language is too small. It:

1. reads a request: a 16-byte tag, a user name, a file name, a body length and a body;
2. compares the tag with a secret key's tag in constant time (rows 1, 2, 13);
3. asks the monitor for permission on the user's record, then reads it (row 7);
4. builds an SQL query from the user name through a sanitizer, and sends it to the `sql` sink (row 3);
5. builds a path under a root from the file name, and sends it to the `fs` sink (row 14);
6. allocates a buffer for the reply, fills it, frees it (row 6);
7. releases one declared value, whether the tag matched (row 4);
8. logs the request with the user name cleaned for the `log` sink (row 3);
9. does all of it within a stated step budget in the body's length (row 10), with no leak under misprediction (row 9);
10. is two components in sequence, authentication and service (row 12).

Then, in March: the reading, the check, the theorem, the QEMU and clang comparison (`test/w32_diff.py`'s method), and the broken variants. Each variant is one row's refused witness written into the handler.

**Rows that were cut** have no variant, and the account says which.

## Log
