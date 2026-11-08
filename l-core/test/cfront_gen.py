#!/usr/bin/env python3
"""RC-01 step 5: write LCore/Slice2/CSrc.lean, the C texts the front end reads, as lists of character codes.

The kernel reduces a list of numerals fast, and a string literal's characters slowly (27 s for these 595 characters), so the texts are codes.
The codes are not trusted for being generated here: CSrc.lean's `run_cmd` reads the vendored file at every build and fails the build if the
two originals are not its lines. The variants are each one stated replacement in the crypto_verify_16 text, shown above its codes.

Usage, from l-core/: python3 test/cfront_gen.py
"""
import hashlib, sys

D = '../third_party/libsodium-1.0.20/'
PINS = [
    ('verify.c', '44642761ec112967330b0bbc67fee47edb9f35e1dd9b4c8a40fb05fc4d568ea9'),
    ('crypto_verify_16.h', 'd3b4fbea4b6d2bf23a9a079939a181625be76a006af129732af86bf4b544456c'),
    ('crypto_verify_32.h', '6ea1ea855b691a2b08510afe74f893d4ff44e40b14501d774d1a73dd79ad4e73'),
    ('LICENSE', '43964d976a6db3fb986af689d05f8ca0e9971878bccae709750dac8fdc4a99cf'),
    # RC-02 step 5: sodium_add, its declaration, and the call and define that fix its length (RC-02-READING section 0)
    ('utils.c', '62ef6a5e2289a69a1e72d8d2d77d7080ee30be1c1e75f758bfdd816e91756d96'),
    ('utils.h', '89e4062d53fa0d43834c83fb2e488a71367a6344b39636d08cc601f942c6f0a5'),
    ('core_ed25519.c', '799dfef3e6ba0a63f36438dedede34a162594aa6ddd616543698a6a3d2fcfed8'),
    ('crypto_core_ed25519.h', 'd8e7c59a0225df93b2d61ea10bbe16550ef7f23d81af8d88e357a58e81af9f6a'),
]
for f, h in PINS:
    if hashlib.sha256(open(D + f, 'rb').read()).hexdigest() != h:
        sys.exit(f + ' does not match its pinned sha256')
raw = open(D + 'verify.c', 'rb').read()
lines = raw.decode('ascii').split('\n')


def excerpt(wrapper_from):
    """Lines 60 to 75 (the portable crypto_verify_n) and the five lines of one wrapper, numbered from 1."""
    return '\n'.join(lines[59:75] + [''] + lines[wrapper_from - 1:wrapper_from + 4]) + '\n'


v16 = excerpt(79)
ulines = open(D + 'utils.c', 'rb').read().decode('ascii').split('\n')
# sodium_add without the HAVE_AMD64_ASM block: lines 313 to 318, then 355 to 360 (RC-02-READING section 0, as corrected)
add = '\n'.join(ulines[312:318] + ulines[354:360]) + '\n'
assert add.startswith('void\nsodium_add(') and 'HAVE_AMD64_ASM' not in add and add.endswith('    }\n}\n')
v32 = excerpt(85)
assert 'crypto_verify_16(' in v16 and 'crypto_verify_32(' in v32

BODY = 'd |= x[i] ^ y[i];'
FOR = 'for (i = 0; i < n; i++) {'
VARIANTS = [
    ('secretIndex', 'a read at a secret index: the front end reads it, and ctCheck refuses it', BODY, 'd |= x[y[i] & 15];'),
    ('earlyExit', 'an early exit at the first difference: `if` and an early `return` are not in the subset', BODY,
     'if (x[i] != y[i]) return -1;'),
    ('division', 'a division: not in the subset', BODY, 'd |= (x[i] ^ y[i]) / 2;'),
    ('uncounted', 'a loop not of the counted form', FOR, 'for (i = 0; d == 0; i++) {'),
    ('pastEnd', 'an index that can pass the end of the array', BODY, 'd |= x[i + 1] ^ y[i];'),
    ('twice', 'one array read twice in a statement, which one temporary cannot hold', BODY, 'd |= x[i] ^ x[i];'),
    ('reservedName', 'a local named as the reading names its counter', 'int i;', 'int i;\n    int c;'),
    ('startAt1', 'a loop that does not start at 0', FOR, 'for (i = 1; i < n; i++) {'),
    ('maskPast', 'a mask that lets the index reach the end', BODY, 'd |= x[y[i] & 16];'),
    ('updateOther', 'a loop whose update names another variable', FOR, 'for (i = 0; i < n; d++) {'),
    ('notInline', 'the called function not `static inline`', 'static inline int', 'int'),
    ('shift64', 'a shift by 64, which C leaves undefined', '>> 8', '>> 64'),
    ('maskedLoop', 'the index masked, so the loop bound is not tied to the length', BODY, 'd |= x[i & 15] ^ y[i & 15];'),
    ('prec', 'C precedence: `&` binds tighter than `^`', BODY, 'd |= x[i] ^ y[i] & 15;'),
    ('precRight', 'the same, parenthesised as C reads it', BODY, 'd |= x[i] ^ (y[i] & 15);'),
    ('precLeft', 'the other parenthesisation', BODY, 'd |= (x[i] ^ y[i]) & 15;'),
]


ADD_STORE = 'a[i] = (unsigned char) c;'
ADD_SHIFT = 'c >>= 8;'
ADD_VARIANTS = [
    ('addWriteConst', 'a write through the read-only parameter', ADD_STORE, 'b[i] = (unsigned char) c;'),
    ('addStorePastEnd', 'a store whose index can pass the end', ADD_STORE, 'a[i + 1] = (unsigned char) c;'),
    ('addWritesIndex', 'a body that writes the loop index', ADD_SHIFT, 'c >>= 8;\n        i += 1;'),
    ('addShift64', 'a shift by 64, which C leaves undefined', ADD_SHIFT, 'c >>= 64;'),
    ('addSecretIndex', 'a store at a secret index: the front end reads it, and ctOutCheck refuses it', ADD_STORE,
     'a[b[i] & 31] = (unsigned char) c;'),
    ('addReturns', 'a value returned from a `void` function', '    }\n}\n', '    }\n    return c;\n}\n'),
    ('addSpacedOp', '`+ =` with a space, which is not C\'s `+=`', 'c += ', 'c + = '),
    ('addInt', 'the same body in a function declared `int`, which a direct entry must not be', 'void\nsodium_add', 'int\nsodium_add'),
    ('addStartAt1', 'a loop that does not start at 0', 'for (i = 0U;', 'for (i = 1U;'),
    ('addUpdateOther', 'a loop whose update names another variable', 'i++) {', 'c++) {'),
]


def codes(s):
    assert all(ord(c) < 128 for c in s)
    out, row = [], []
    for c in s:
        row.append(str(ord(c)))
        if len(row) == 30:
            out.append(', '.join(row))
            row = []
    if row:
        out.append(', '.join(row))
    return '[\n  ' + ',\n  '.join(out) + ']'


def comment(s):
    return '\n'.join('    ' + l for l in s.rstrip('\n').split('\n'))


parts = ['''/-
  RC-01 step 5: the C texts the front end reads, as character codes. Generated by `test/cfront_gen.py`; do not edit.

  The originals are pinned. The `#eval` below runs whenever this file is compiled, and fails the compile unless:
  - the vendored `verify.c`, both headers and the licence hash, by `Sha256`, to the release's sha256 (`PINS`), and `Sha256` passes its
    self-test;
  - each original is exactly its lines of `verify.c` (60 to 75, then 79 to 83 or 85 to 89);
  - the headers define the two lengths as read;
  - RC-02: `addC` is lines 313 to 318 and 355 to 360 of the vendored `utils.c`, its declaration is line 54 of `utils.h`, line 164 of
    `core_ed25519.c` calls it at `crypto_core_ed25519_SCALARBYTES`, and the header defines that as 32.
  The pins are in an ordinary file, so an agent could still edit a pin and its copy together. TP-01 asks for them under the user's key.
  **Not at every build:** Lake does not track the vendored files, so an edit to one alone is caught only when this file is recompiled.
-/
import LCore.Slice2.Sha256

namespace LCore.Slice2.CSrc
''']
parts.append(f'/-- `crypto_verify_n` and `crypto_verify_16`, from libsodium 1.0.20-RELEASE `verify.c`:\n\n```c\n{v16}```\n-/\ndef verify16C : List Nat := {codes(v16)}\n')
parts.append(f'/-- `crypto_verify_n` and `crypto_verify_32`, from the same file. -/\ndef verify32C : List Nat := {codes(v32)}\n')
parts.append(f'/-- `sodium_add`, from libsodium 1.0.20-RELEASE `utils.c`, lines 313 to 318 and 355 to 360:\n\n```c\n{add}```\n-/\ndef addC : List Nat := {codes(add)}\n')
for name, why, old, new in ADD_VARIANTS:
    assert add.count(old) == 1, name
    parts.append(f'/-- **Variant of `sodium_add`**, {why}: `{old.strip()}` becomes `{new.strip()}`. -/\ndef {name}C : List Nat := {codes(add.replace(old, new))}\n')
for name, why, old, new in VARIANTS:
    assert v16.count(old) == 1, name
    parts.append(f'/-- **Variant**, {why}: `{old}` becomes `{new}`. -/\ndef {name}C : List Nat := {codes(v16.replace(old, new))}\n')
parts.append('/-- The release\'s sha256 for each vendored file, as `RC-01-READING` records them. -/\ndef PINS : List (String × String) := [\n' +
             ',\n'.join(f'  ("{f}", "{h}")' for f, h in PINS) + ']\n')
parts.append('''/-! **The pin**, checked whenever this file is compiled: an error here fails it. Lake recompiles this file when its own text
    changes, not when a vendored file does, so a cached build does not rerun it (RC-02 step 5, `TP-01`). -/
#eval show IO Unit from do
  unless Sha256.selfTest do throw (IO.userError "Sha256 fails its self-test")
  for (f, h) in PINS do
    let b ← IO.FS.readBinFile ("../third_party/libsodium-1.0.20/" ++ f)
    unless Sha256.sha256 b.toList == h do throw (IO.userError s!"{f} does not hash to its pinned sha256")
  let t ← IO.FS.readFile "../third_party/libsodium-1.0.20/verify.c"
  let ls := t.splitOn "\\n"
  let ex (w : Nat) : String := String.intercalate "\\n" ((ls.drop 59).take 16 ++ [""] ++ (ls.drop (w - 1)).take 5) ++ "\\n"
  let as (s : String) : List Nat := s.toList.map Char.toNat
  unless as (ex 79) == verify16C do throw (IO.userError "verify16C is not lines 60-75 and 79-83 of the vendored verify.c")
  unless as (ex 85) == verify32C do throw (IO.userError "verify32C is not lines 60-75 and 85-89 of the vendored verify.c")
  let h16 ← IO.FS.readFile "../third_party/libsodium-1.0.20/crypto_verify_16.h"
  let h32 ← IO.FS.readFile "../third_party/libsodium-1.0.20/crypto_verify_32.h"
  unless (h16.splitOn "\\n").contains "#define crypto_verify_16_BYTES 16U" do throw (IO.userError "crypto_verify_16_BYTES is not 16U")
  unless (h32.splitOn "\\n").contains "#define crypto_verify_32_BYTES 32U" do throw (IO.userError "crypto_verify_32_BYTES is not 32U")
  -- RC-02: sodium_add, its declaration, its call at the length read, and the define
  let u ← IO.FS.readFile "../third_party/libsodium-1.0.20/utils.c"
  let ul := u.splitOn "\\n"
  unless as (String.intercalate "\\n" ((ul.drop 312).take 6 ++ (ul.drop 354).take 6) ++ "\\n") == addC do
    throw (IO.userError "addC is not lines 313-318 and 355-360 of the vendored utils.c")
  let uh ← IO.FS.readFile "../third_party/libsodium-1.0.20/utils.h"
  unless (uh.splitOn "\\n")[53]? == some "void sodium_add(unsigned char *a, const unsigned char *b, const size_t len);" do
    throw (IO.userError "utils.h line 54 is not sodium_add's declaration")
  let ce ← IO.FS.readFile "../third_party/libsodium-1.0.20/core_ed25519.c"
  unless (ce.splitOn "\\n")[163]? == some "    sodium_add(x_, y_, crypto_core_ed25519_SCALARBYTES);" do
    throw (IO.userError "core_ed25519.c line 164 is not the call that fixes the length")
  let ch ← IO.FS.readFile "../third_party/libsodium-1.0.20/crypto_core_ed25519.h"
  unless (ch.splitOn "\\n").contains "#define crypto_core_ed25519_SCALARBYTES 32" do
    throw (IO.userError "crypto_core_ed25519_SCALARBYTES is not 32")

end LCore.Slice2.CSrc
''')
open('LCore/Slice2/CSrc.lean', 'w').write('\n'.join(parts))
print('wrote LCore/Slice2/CSrc.lean')
