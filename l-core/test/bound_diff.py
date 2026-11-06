#!/usr/bin/env python3
"""BOUND-01 step 5: the budgets on the bytes, under QEMU.

`countUp_bytes_budget` says the 104-byte image of `countUp` runs at most `8 * (4n + 2) + 5` instructions, with `n` the public word, and
`capped_bound_bytes` says the image of `capped` runs at most 97, on every input (BOUND-01 step 5a; before it, ~~`26 * (4n + 2) + 26`~~
and ~~672~~). Here QEMU runs both on many inputs, including ones far past the
cap, and each run's instruction count, PCs, addresses and result are compared with the model and then with the budget.

  model     every run equals the model's prediction: PCs, addresses, result, cost, outcome
  budget    every run's instruction count is at most the proved budget
  secret    the secret word changes nothing, so the budget really is a function of the public word
  vacuity   the comparison can fail: the machine's exact cost, 19n + 9 for countUp and 83 past the cap for capped, is measured, and a
            budget one below it is seen to be exceeded

This measures how close the budgets are to what the machine runs. It says nothing about QEMU's fidelity to hardware, or about time.

Usage, from l-core/: python3 test/bound_diff.py <scratch directory>
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from image2_diff import literal, write, observe, predictions  # noqa: E402

BYTES = "LCore/Slice2/BoundBytes.lean"
COUNT_N = [0, 1, 2, 3, 7, 10, 63, 64, 65, 100, 300]
CAP_N = [0, 1, 2, 3, 4, 5, 10, 1000, 2 ** 32, 2 ** 63, 2 ** 64 - 1]
SECRETS = [0, 1, 6, 2 ** 63, 2 ** 64 - 1]
FUEL = 20000


def count_budget(n):
    return 8 * (4 * n + 2) + 5


def main():
    d = os.path.abspath(sys.argv[1])
    os.makedirs(d, exist_ok=True)
    img = {"countUp": literal("countUpNats", BYTES), "capped": literal("cappedNats", BYTES)}
    if None in img.values():
        print("bound-diff: a literal was not found")
        return 2
    cases = [("countUp", s, n, FUEL) for n in COUNT_N for s in SECRETS] + [("capped", s, n, FUEL) for n in CAP_N for s in SECRETS]
    preds = predictions(d, cases)
    bad = 0
    obs = {}
    for i, s, n, f in cases:
        o = observe(write(d, "r", img[i], s, n), img[i], {}, [], f"{d}/r.log")
        m = preds[(i, s, n, f)]
        if o is None or m["out"] != "done" or o["rc"] < 0 or o["trace"] != m["trace"] or o["cost"] != m["cost"] or o["a0"] != m["ret"]:
            print(f"FAIL model {i} ({s}, {n})")
            bad += 1
            continue
        obs[(i, s, n)] = o
    if not bad:
        print(f"ok   model: {len(cases)} runs, every PC, address, result and cost equal the model's")

    over = [(i, s, n) for (i, s, n), o in obs.items() if o["cost"] > (count_budget(n) if i == "countUp" else 97)]
    if over:
        print(f"FAIL budget: exceeded on {over[:3]}")
        bad += 1
    else:
        worst = max(o["cost"] / count_budget(n) for (i, s, n), o in obs.items() if i == "countUp")
        cap_max = max(o["cost"] for (i, s, n), o in obs.items() if i == "capped")
        print(f"ok   budget: every run within it. countUp uses at most {worst:.0%} of its budget; capped runs at most {cap_max} "
              f"of 97, at inputs up to 2^64 - 1")

    leaks = sum(1 for (i, s, n), o in obs.items() if (o["trace"], o["cost"]) != (obs[(i, SECRETS[0], n)]["trace"], obs[(i, SECRETS[0], n)]["cost"]))
    if leaks:
        print(f"FAIL secret: {leaks} runs differ from the same public word's first")
        bad += 1
    else:
        print(f"ok   secret: {len(obs) - len(COUNT_N) - len(CAP_N)} comparisons, the secret changes neither trace nor cost")

    exact = all(obs[("countUp", 0, n)]["cost"] == 19 * n + 9 for n in COUNT_N)
    cap_exact = all(obs[("capped", 0, n)]["cost"] == (51 + 8 * min(n, 4)) for n in CAP_N)
    tight_count = [n for n in COUNT_N if obs[("countUp", 0, n)]["cost"] > 19 * n + 8]
    tight_cap = [n for n in CAP_N if obs[("capped", 0, n)]["cost"] > 82]
    if exact and cap_exact and tight_count == COUNT_N and tight_cap:
        print("ok   vacuity: countUp costs exactly 19n + 9 and capped 51 + 8 min(n, 4), so a budget of 19n + 8, or of 82 for capped, is "
              f"exceeded on every countUp input and on {len(tight_cap)} capped inputs: the check can fail")
    else:
        print(f"FAIL vacuity: exact {exact} {cap_exact}, exceeded {tight_count} {tight_cap}")
        bad += 1

    print(f"bound-diff: {bad} failed")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
