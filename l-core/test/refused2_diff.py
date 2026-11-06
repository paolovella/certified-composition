#!/usr/bin/env python3
"""VS-2 step 9: the refused programs' literal images under QEMU. Each pair of runs differing only in the secret word is compared with the
model and with each other, through the channel `Slice2/Teeth.lean` names for that program.

The bytes are read from Teeth.lean's text; ELF writing, address derivation and QEMU control are image2_diff.py's.

  model     every run's PCs, addresses, result, cost and outcome equal the model's at the same fuel
  leak      the secret shows, and only where the theorem says: an address with the PCs, cost and result equal (secretStore); the result
            with the trace equal (throughArray); when, and whether, the run finishes (secretLoop); the PCs (secondIter, arrayInLoop)
  control   the accepted scan, run the same way on the same secrets, shows no difference

Usage, from l-core/: python3 test/refused2_diff.py <scratch directory>
"""
import os
import struct
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from image2_diff import literal, write, observe, predictions  # noqa: E402

TEETH = "LCore/Slice2/Teeth.lean"
NAMES = ["secretLoad", "secretStore", "secretLoop", "secondIter", "throughArray", "arrayInLoop"]
# (secret, secret', public, fuel): the pair each theorem uses, and the fuel the model is run at.
PAIRS = {
    "secretLoad": (1, 2, 1, 400), "secretStore": (1, 2, 1, 400), "secretLoop": (1, 2, 1, 400),
    "secondIter": (0, 5, 1, 400), "throughArray": (1, 2, 1, 400), "arrayInLoop": (0, 5, 1, 400),
}
NEVER = 2 ** 63
STOP = 400


def main():
    d = os.path.abspath(sys.argv[1])
    os.makedirs(d, exist_ok=True)
    img = {n: literal(n + "Nats", TEETH) for n in NAMES}
    img["scan"] = literal("scanNats")
    if None in img.values():
        print("refused2-diff: a literal was not found")
        return 2
    cases = []
    for n, (a, a2, b, f) in PAIRS.items():
        cases += [(n, a, b, f), (n, a2, b, f)]
    cases += [("secretLoop", NEVER, 1, STOP), ("scan", 0, 1, 200), ("scan", 5, 1, 200), ("scan", 1, 1, 200), ("scan", 2, 1, 200)]
    preds = predictions(d, cases)
    bad = 0

    obs = {}
    for i, a, b, f in cases:
        limit = STOP if a == NEVER else None
        o = observe(write(d, "r", img[i], a, b), img[i], {}, [], f"{d}/r.log", limit=limit)
        m = preds[(i, a, b, f)]
        if o is None:
            print(f"FAIL {i} ({a}, {b}): QEMU gave no verdict")
            bad += 1
            continue
        if limit is None:
            same = m["out"] == "done" and o["trace"] == m["trace"] and o["cost"] == m["cost"] and o["a0"] == m["ret"]
        else:
            same = o["stopped"] and m["out"] == "fuel" and o["trace"] == m["trace"]
        if not same:
            print(f"FAIL {i} ({a}, {b}): QEMU differs from the model")
            bad += 1
        obs[(i, a)] = o
    if not bad:
        print(f"ok   model: {len(cases)} runs, every PC, address, result, cost and outcome equal the model's")

    pcs = lambda o: [x for x in o["trace"] if x[0] == "P"]
    addrs = lambda o: [x for x in o["trace"] if x[0] == "A"]
    want = {
        "secretLoad": lambda o, p: addrs(o) != addrs(p),
        "secretStore": lambda o, p: addrs(o) != addrs(p) and pcs(o) == pcs(p) and o["cost"] == p["cost"] and o["a0"] == p["a0"],
        "secretLoop": lambda o, p: o["cost"] != p["cost"],
        "secondIter": lambda o, p: pcs(o) != pcs(p),
        "throughArray": lambda o, p: o["trace"] == p["trace"] and o["a0"] != p["a0"],
        "arrayInLoop": lambda o, p: pcs(o) != pcs(p),
    }
    for n, (a, a2, b, f) in PAIRS.items():
        o, p = obs.get((n, a)), obs.get((n, a2))
        if o is None or p is None or not want[n](o, p):
            print(f"FAIL leak {n}: not seen where the theorem says")
            bad += 1
        else:
            print(f"ok   leak {n}: secrets {a} and {a2} differ under QEMU as Teeth.lean says (costs {o['cost']}, {p['cost']})")
    lo, hi = obs.get(("secretLoop", 1)), obs.get(("secretLoop", NEVER))
    if lo is None or hi is None or not hi["stopped"] or lo["stopped"]:
        print("FAIL leak secretLoop, whether: not seen")
        bad += 1
    else:
        print(f"ok   leak secretLoop, whether: secret 1 exits after {lo['cost']} instructions, secret 2^63 is still running at {STOP}, "
              "stopped by the harness")

    c = [obs.get(("scan", a)) for a in (0, 5, 1, 2)]
    if None in c or c[0]["trace"] != c[1]["trace"] or c[2]["trace"] != c[3]["trace"] or c[0]["cost"] != c[1]["cost"]:
        print("FAIL control: the accepted scan shows a difference")
        bad += 1
    else:
        print("ok   control: the accepted scan, on the same secret pairs, shows none")

    print(f"refused2-diff: {bad} failed")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
