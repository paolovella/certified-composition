# External corpus — transcribed from CWE demonstrative examples

Not written by me. Each program is a faithful transcription of a published CWE
demonstrative example into this language, keeping the control and data flow of the
original. Where the original relies on a language feature this one lacks, the case is
recorded as INEXPRESSIBLE rather than adapted until it fits.

All programs were written before the checker was run once.

| id | source | label | original |
|---|---|---|---|
| b01 | CWE-416 ex.1 | bad | malloc buf2, free it, malloc twice more, then `strncpy` into the freed `buf2R1` |
| b02 | CWE-416 ex.2 | bad | `if (err) { abrt=1; free(ptr); } ... if (abrt) logError(..., ptr);` |
| b03 | CWE-416 ex.2 | good | the same flow with the use before the free (the implied fix) |
| b04 | CWE-862 ex.1 | bad | query the employee DB with no authorization check at all |
| b05 | CWE-862 ex.1 | good | the same read, authorization checked first |
| b06 | CWE-401 ex.1 | bad | `malloc`, then return on the error path without `free` |
| b07 | CWE-89 ex.1 | bad | query built by string concatenation with untrusted input |
| b08 | CWE-89 ex.5 | good | the same query with the input validated/converted first |
| b09 | CWE-835 ex.1 | bad | `do { connect } while (connected < 0)` — retries forever |
| b10 | CWE-835 ex.1 | good | `while (connected < 0 && count < MAX_ATTEMPTS)` — bounded retry |
| b11 | CWE-835 ex.2 | bad | `while (inventoryCount > minimumCount) inventoryCount -= rateSold;` — never decreases if `rateSold == 0` |
| b12 | CWE-835 ex.2 | good | the same loop, guarded by an up-front `if (rateSold < 1) return;` |

## Inexpressible

| source | why |
|---|---|
| CWE-862 ex.2 | the flaw is that the record's owner is not compared to the authenticated user. This language has **no subject** — brick 35 already recorded IDOR (CWE-639) as a named follow-on |
| CWE-401 ex.1, faithfully | the leak happens on an **early return**. There is no early return in this language; b06 keeps the branch structure but not the return |
