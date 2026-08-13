# Corpus task list — written BEFORE any program, and before running the checker

Method: each task states what a handler must *do*, in prose, taken from ordinary
request-handler patterns and CWE Top-25 categories. Each program is then written the most
natural way the language allows. The checker is run only after all programs exist.

Outcome categories:
  ACCEPTED      — the checker certifies it
  REJECTED      — expressible, but refused by a rule (record which)
  INEXPRESSIBLE — the task cannot be written in this language at all

 1. Authorize a resource, then read it.
 2. Authorize two resources, read both.
 3. Read an authorized resource once per item, for a bounded number of items.
 4. Allocate a buffer, write to it, read it back, free it.
 5. Allocate two buffers, use both, free both.
 6. Copy a value from one heap cell to another.
 7. Build a parameterized query from untrusted input and emit it.
 8. Emit a constant message containing no untrusted data.
 9. Emit an untrusted value with no sanitization (should be refused).
10. Branch on a public flag; read a different resource in each branch.
11. Branch on a public flag; allocate in one branch only, free after.
12. Accumulate a running total over a bounded number of iterations.
13. Free a buffer only when a public flag is set.
14. Read a secret into a secret variable and never emit it.
15. Swap the contents of two heap cells.
16. Zero a buffer, then free it.
17. Retry a mediated read a bounded number of times.
18. Do the authorized work only after the check succeeds.
19. Copy from one buffer to another through pointers.
20. Allocate and free a scratch cell on every iteration of a bounded loop.
21. Allocate on every iteration of a bounded loop, free once after the loop.
22. Validate input into a sanitized variable, then emit it twice.
23. Emit two different queries from the same untrusted input.
24. Nested bounded loops doing heap work.
25. Read the same authorized resource in both branches of a public branch.
26. Copy N items from one buffer to another, indexed by the loop counter.
27. Factor the query-building into a helper used from two call sites.
28. Return early from the handler when the check fails.
29. Read one field of a record held in a buffer.
30. Retry until a condition holds, with no fixed bound.
