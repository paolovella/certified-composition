#!/usr/bin/env python3
"""S-USABLE S3: what each added construct cost, from git history.

For each commit that added a construct, the lines added and removed in l-core/LCore, by layer:
  machine   Slice/Rv.lean, Slice/Word.lean          (the RV64 model)
  source    Slice/Source.lean, Slice2/Source.lean   (semantics, checker, noninterference)
  slots     Slice/Slots.lean, Slice2/Slots.lean     (pass 1: names to slots)
  lower     Slice/Lower.lean, Slice2/{Lower,Chunk,Pass}.lean   (pass 2: slots to bytes, and its PassCert)
  budget    Slice2/Budget.lean, Slice2/For.lean
  witness   everything else under LCore (programs, teeth, images)
and whether the kernel (LCore/Kernel) changed. "Removed" counts lines an existing proof lost, which is the edit to
existing work that PLAN-2026-10 section 6 says a new construct should not need.

Usage, from the repo root: python3 research/2026-11/usable/s3_cost.py > bench/usable/s3.tsv
"""
import subprocess

COMMITS = [
    ("b2c3026", "RC-01 2a", "5 ALU instructions in the machine"),
    ("934ea34", "RC-01 2b", "^ | & - and >> k in the language"),
    ("f9df3c6", "RC-01 3a", "lbu in the machine"),
    ("930edb5", "RC-01 3", "loadB: byte arrays as inputs"),
    ("e54172b", "RC-01 4", "ctCheck and the widened loop rule"),
    ("ec359bc", "VS-2 3", "andi in the machine"),
    ("bde850b", "VS-2 4", "while, and an array at a public index (source)"),
    ("8157fee", "VS-2 5", "the same, through slots"),
    ("e31d9c9", "VS-2 6", "the same, through the lowering"),
    ("0bd40ae", "BOUND-01 2", "counted loops forN, forMax"),
    ("44ec2c5", "BOUND-01 3", "the checker's budget over counted loops"),
]


def layer(path):
    p = path.replace("l-core/LCore/", "")
    if p.startswith("Kernel/"):
        return "kernel"
    if p in ("Slice/Rv.lean", "Slice/Word.lean"):
        return "machine"
    if p.endswith("Source.lean") and p.startswith("Slice"):
        return "source"
    if p.endswith("Slots.lean") and p.startswith("Slice"):
        return "slots"
    if p in ("Slice/Lower.lean", "Slice2/Lower.lean", "Slice2/Chunk.lean", "Slice2/Pass.lean"):
        return "lower"
    if p in ("Slice2/Budget.lean", "Slice2/For.lean"):
        return "budget"
    return "witness"


LAYERS = ["machine", "source", "slots", "lower", "budget", "witness", "kernel"]


def main():
    print("commit\tstep\tconstruct\t" + "\t".join(f"{l}_add\t{l}_del" for l in LAYERS) + "\tfiles")
    for h, step, what in COMMITS:
        out = subprocess.run(["git", "show", "--numstat", "--format=", h, "--", "l-core/LCore"],
                             capture_output=True, text=True, check=True).stdout
        add = {l: 0 for l in LAYERS}
        dele = {l: 0 for l in LAYERS}
        files = 0
        for line in out.splitlines():
            a, d, path = line.split("\t")
            if not path.endswith(".lean"):
                continue
            files += 1
            l = layer(path)
            add[l] += int(a)
            dele[l] += int(d)
        print(f"{h}\t{step}\t{what}\t" + "\t".join(f"{add[l]}\t{dele[l]}" for l in LAYERS) + f"\t{files}")


if __name__ == "__main__":
    main()
