# The `.uc` language: reference for program authors (v2)

*v2, 2026-10-28 (EXPR-01). v1 (`REFERENCE.md`) is the frozen input of S-EXPR and stays as it
was. The only change: the rule for `secret` cells, which v1 left out.*

This is everything you get. You do not have the checker's source and cannot run it. Write
each program the most natural way the language allows.

## What a checked program is promised

A tool reads a `.uc` file and either certifies it or refuses it. A certified program has:
- a cost budget that holds for every input;
- every `access` to a resource authorized by an earlier `check`;
- no secret value influencing anything public, including which branch runs and how long the
  program takes;
- memory safety: no use of a freed or never-allocated pointer, and no double free;
- no injection: untrusted text reaches a sink only through `san`.

## Lexical rules

- **Tokens are separated by whitespace, and every token must be.** Write `( a + b )`, not
  `(a+b)`; `san ( input )`, not `san(input)`; `{` and `}` need spaces around them.
- **Identifiers:** any whitespace-free word that is not a keyword or a number and contains no
  `"`.
- **Integers:** `0`, `42`, `-3`.
- **String literals:** `"..."` with **no spaces inside**. Inside a literal, `'` is the quote
  delimiter a sink cares about; every other character is ordinary text. For example `"abc"` or
  `"'"`.
- There are **no comments**.

Keywords: `skip let check access alloc secret deref free load store sset emit if else while for
san ( ) { } ; = + ++`.

## Programs

A program is statements separated by `;`. There is no trailing `;`, and the whole file is one
program.

| Statement | Meaning |
|---|---|
| `skip` | does nothing |
| `let x = E` | integer variable `x` gets the value of `E` |
| `check r` | asks the monitor for authority over resource `r`; on success, later accesses to `r` are authorized |
| `access r` | reads resource `r` (for example `db`, `profile`, `cache`) |
| `alloc p` | allocates a fresh heap cell; `p` holds its pointer |
| `secret p` | allocates a fresh heap cell meant to hold secret data; **`p` itself must be listed as secret in the manifest**, or the program is refused |
| `deref p` | reads through pointer `p` |
| `load d p` | integer variable `d` gets the contents of the cell `p` points to |
| `store p v` | the cell `p` points to gets the value of integer variable `v` |
| `free p` | frees the cell `p` points to |
| `sset x S` | string variable `x` gets the value of string expression `S` |
| `emit k S` | sends string `S` to sink `k` (for example `db`, `sh`, `log`, `fs`, `html`) |
| `if E { P } else { P }` | runs the first block if `E` is not zero, else the second; `else` is required (use `skip`) |
| `while E { P }` | repeats the block while `E` is not zero |
| `for i = K { P }` | runs the block exactly `K` times; `K` is a literal non-negative integer and `i` is the counter |

Integer expressions `E`: an integer literal, a variable, or `( E + E )`. There is no other
arithmetic and no comparison operator.

String expressions `S`: a literal, a string variable, `( S ++ S )` for concatenation, or
`san ( S )`, which sanitizes untrusted text for a sink.

- The string variable `input` holds untrusted request data.
- Variables can be marked **secret** per program (in the manifest). A secret is any value that
  must not leak: a password, a key or a token. The pointer of every `secret` cell must be marked
  too.
- Integers are unbounded mathematical integers. There are no functions, procedures, arrays,
  records, early return, exceptions or concurrency.

Example, a handler that is certified:

```
check db ;
alloc buf ;
for n = 5 {
  access db ;
  alloc t ;
  store t z ;
  emit db ( "'" ++ ( san ( input ) ++ "'" ) ) ;
  free t
} ;
free buf
```
