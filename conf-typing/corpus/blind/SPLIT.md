# Split (S-EXPR step 2)

Python `random.Random(20261028)`, stratified: the SAFE and UNSAFE ids are each shuffled, and the first 16 SAFE and first 4 UNSAFE go to the holdout.
The holdout's programs are written with the rest, but are not run through `certcheck` until the open half is reported, and no rule changes in between.

open: 1 2 3 5 7 8 9 15 16 18 19 20 22 23 28 29 33 36 37 40

holdout: 4 6 10 11 12 13 14 17 21 24 25 26 27 30 31 32 34 35 38 39
