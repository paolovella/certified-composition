# Brief: write a task list for a secure request-handler language

You are writing the test tasks for measuring a small security-checked programming language.
You have not seen the language and will not: that is deliberate. Its authors want to know how
many ordinary tasks it can express and certify, so the tasks must come from what real code
needs, not from what the language happens to have.

**What the language is for.** Small server-side request handlers that must be secure by
construction:
- they authorize access to named resources before using them;
- they allocate, use and free heap buffers;
- they combine untrusted input into strings sent to sinks such as a database, a shell, a log, a
  file path or HTML;
- they hold secrets (passwords, keys, tokens) that must not leak, including through timing or
  through which branch runs;
- they loop over bounded work and must finish within a cost budget.

It checks properties such as:
- every access is authorized;
- no use-after-free, double free or wild pointer;
- no injection into a sink;
- no secret reaches public output or decides a branch;
- loops are bounded.

**Your task.** Write `TASKS.md` in this directory with exactly **40** numbered tasks.
- Draw on the CWE Top 25 (injection, path traversal, missing authorization, use-after-free,
  double free, out-of-bounds, sensitive-data exposure, timing leaks, resource exhaustion) and
  on ordinary handler patterns: login, retry, pagination, caching, batch processing, parsing
  then emitting, cleanup on every path, nested loops, conditional allocation, stored data
  read back later.
- Each task is 1–3 sentences of prose. Give what the handler must do, and end with the property
  it must satisfy in brackets, e.g. `[must not leak the password]`.
- Mark each task **SAFE** (a correct program exists that should be certified) or **UNSAFE** (the
  task asks for something insecure that a checker should refuse). Aim for about 32 SAFE and
  8 UNSAFE.
- Vary difficulty. Include tasks you suspect a small language may be unable to express, such as
  functions, arrays, records, early return, error handling or concurrency. Do not leave out a
  realistic task because it seems hard.
- Do not invent syntax or write code.

The file format: a title line, one blank line, then lines `NN. [SAFE|UNSAFE] text [property]`.
Write only that file.
