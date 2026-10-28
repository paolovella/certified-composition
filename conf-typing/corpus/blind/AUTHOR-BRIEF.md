# Brief: write one program per task

In this directory:
- `REFERENCE.md` is the language, and it is all you get.
- `TASKS.md` holds 40 tasks.

For **every** task `NN`, do exactly one of the following:

- **Write `NN.uc`.** Write the program the most natural way the language allows.
  - For a **SAFE** task, write a correct program that does what the task asks.
  - For an **UNSAFE** task, write the program the task describes, insecure behaviour included.
    The point is to see whether the checker refuses it, so do not fix it.
  - Where the language lacks something the task needs, approximate it faithfully when the
    approximation keeps the task's point. A resource or sink can stand for an external call, and
    a counted loop for a bounded list. Say what you approximated.
- **Or declare it inexpressible** when no faithful program exists. Do not write a program that
  quietly drops the task's point.

Then write `MANIFEST.tsv` with one line per task, in tab-separated columns:

```
NN	file-or-none	secrets	note
```

- **`file-or-none`:** `NN.uc`, or `none` if the task is inexpressible.
- **`secrets`:** comma-separated integer variable names that hold secrets in this program, or `-`.
- **`note`:**
  - for an inexpressible task: one sentence on what is missing;
  - otherwise: what you approximated, or `-`.

Number tasks with two digits (`01` … `40`).

Rules:
- Use only what `REFERENCE.md` describes, and follow its lexical rules exactly. Every token is
  separated by whitespace.
- Do not try to read anything outside this directory. You cannot run the checker.
- Write the files, and nothing else.
