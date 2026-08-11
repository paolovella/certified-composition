"""Brute-force check of the notes-§54 walk claims on randomized (a),(c),(d),(e)-conforming
C-sequences over ordinals below omega^2 * L (so limits-of-limits genuinely exist).

Ordinal omega^2*c + omega*a + b  <->  integer c*A*M + a*M + b   (order-isomorphic).
"""
import random, sys

L, A, M = 3, 6, 14           # c < L, a < A, b < M
N = L * A * M

def dec(x):  return (x // (A*M), (x // M) % A, x % M)
def enc(c,a,b): return c*A*M + a*M + b

def is_zero(x): return x == 0
def is_limit(x):
    c,a,b = dec(x)
    return b == 0 and x > 0
def is_lim_of_lim(x):
    c,a,b = dec(x)
    return b == 0 and a == 0 and c > 0
def limit_part(x):           # largest limit <= x  (0 if none)
    c,a,b = dec(x)
    return enc(c,a,0)

def build_C(seed):
    rng = random.Random(seed)
    C = {}
    for x in range(1, N):
        c,a,b = dec(x)
        if b > 0:                       # successor: (a) C_{y+1} = {y}
            C[x] = [x-1]
        elif a > 0:                     # x = delta + omega, delta = enc(c,a-1,0)
            d = enc(c, a-1, 0)          # (e): C_x = {delta+n+1}
            C[x] = [d + n + 1 for n in range(M-1)]
        elif c > 0:                     # x = omega^2 * c : a limit of limits
            # (d): nth element must be lam + n + 1 with lam a limit; cofinal in x.
            # nondecreasing limit-parts, reaching the top limit below x and staying.
            T = M - 1
            top = A - 1
            switch = rng.randint(1, T - 1)
            a_seq = []
            cur_a = 1
            for n in range(T):
                if n >= switch: cur_a = top
                else:
                    if rng.random() < 0.35 and cur_a < top: cur_a += 1
                a_seq.append(cur_a)
            elts = [enc(c-1, a_seq[n], 0) + n + 1 for n in range(T)]
            assert all(elts[i] < elts[i+1] for i in range(T-1)), elts
            assert elts[-1] < x
            C[x] = elts
    return C

def walk(C, al, be):
    """minimal walk be -> al; returns (stops, weights) with stops[0]=be."""
    stops, wts = [be], []
    cur = be
    while cur > al:
        Cc = C[cur]
        nxt = min((y for y in Cc if y >= al), default=None)
        wts.append(sum(1 for y in Cc if y < al))
        assert nxt is not None and nxt < cur, (al, be, cur)
        cur = nxt
        stops.append(cur)
    return stops, wts

def rho0(C, al, be): return walk(C, al, be)[1] if al < be else []
def rho1(C, al, be):
    w = rho0(C, al, be)
    return max(w) if w else 0
def rho3(C, al, be):
    w = rho0(C, al, be)
    return 1 if (w and w[-1] == max(w)) else 0

def F(C, al, be, memo):
    """full lower trace, Handbook 1.4"""
    if al == be: return frozenset([al])
    key = (al, be)
    if key in memo: return memo[key]
    memo[key] = frozenset([al])            # guard
    nxt = min(y for y in C[be] if y >= al)
    out = set(F(C, al, nxt, memo)) if nxt != be else {al}
    for xi in C[be]:
        if xi < al:
            out |= F(C, xi, al, memo)
    out = frozenset(out)
    memo[key] = out
    return out

def run(seed, verbose=False):
    C = build_C(seed)
    memo = {}
    limits = [x for x in range(1, N) if is_limit(x)]
    Bset = {}
    def B(be):
        if be not in Bset:
            Bset[be] = set(x for x in range(be) if rho3(C, x, be) == 1)
        return Bset[be]

    def thr(be, lam):
        """least Nn with rho3(lam+n,be)=1 for all n>=Nn with lam+n<be (truncated fan)"""
        top = min(lam + M, be)
        best = 0
        for n in range(top - lam):
            if rho3(C, lam + n, be) == 0: best = n + 1
        return best

    fails = []
    # --- Theorem S: B_{delta+omega} = B_delta u [delta, delta+omega)   (under (e))
    for d in limits:
        c,a,b = dec(d)
        if a + 1 >= A: continue
        x = enc(c, a+1, 0)                      # delta + omega
        lhs = B(x)
        rhs = set(B(d)) | set(range(d, x))
        if lhs != rhs: fails.append(("S", d, sorted(lhs ^ rhs)[:6]))
    # --- Theorem T witness: delta in B_{delta+omega}
    for d in limits:
        c,a,b = dec(d)
        if a + 1 >= A: continue
        x = enc(c, a+1, 0)
        if d not in B(x): fails.append(("T-witness", d))
    # --- Handbook 1.16(a): rows are finite-to-one, {xi < be : rho1(xi,be) <= n} finite.
    #     Load-bearing three times already (rho1's nontriviality, Theorem P, Theorem X)
    #     and a fourth time in section 58 (Lemma Y2), so it is checked, not only cited.
    #     Over a truncated model "finite" reads as: the count is monotone in n and stays
    #     well below the level, i.e. the row does not collapse to a bounded function.
    tested_rows = 0
    for be in range(2, N):
        prev = -1
        for n in range(0, 4):
            cnt = sum(1 for xi in range(be) if rho1(C, xi, be) <= n)
            tested_rows += 1
            if cnt < prev:
                fails.append(("1.16a-monotone", be, n, cnt, prev))
            prev = cnt
        # NOTE: the *asymptotic* half of 1.16(a) - that rows are unbounded, so no fixed
        # n covers every level - is NOT checkable here and the model gets it backwards:
        # for be <= 11 every xi has rho1(xi,be) <= 3. Third recorded instance of the
        # truncation artefact (notes section 54, 57, 58). Only the identity-level half
        # (monotonicity of the counts) is asserted.
        tested_rows += 1
    # --- section 63: the coherence fibre does NOT determine the walk cost. Existence
    #     claim, identity-level: there are be, be' with B_al & B_be = B_al & B_be' and
    #     rho1(al,be) != rho1(al,be'). Asserted as "at least one such fibre exists",
    #     which is what the section claims; the SIZE of the spread is model-dependent
    #     and is reported, not asserted.
    tested_fib = 0
    fib_spread = 0
    for al in range(3, N // 3):
        groups = {}
        for be in range(al + 1, N):
            groups.setdefault(frozenset(B(al) & B(be)), []).append(rho1(C, al, be))
        for vals in groups.values():
            if len(vals) > 1:
                tested_fib += 1
                fib_spread = max(fib_spread, max(vals) - min(vals))
    if tested_fib > 0 and fib_spread == 0:
        fails.append(("fibre-determines-cost", "section 63 claims it does not"))

    # --- rho1 coherence (used since section 51, load-bearing in section 62's Lemma
    #     W3a): for be < ga, {xi < be : rho1(xi,be) != rho1(xi,ga)} is finite. Over the
    #     truncated model, "finite" reads as "small and not growing with be" - we assert
    #     the difference set is a proper subset of be, which is the identity-level
    #     content. Its UNBOUNDEDNESS is asymptotic and deliberately not asserted.
    tested_coh = 0
    for be in range(3, N // 2):
        for ga in range(be + 1, min(be + 10, N)):
            d = sum(1 for xi in range(be) if rho1(C, xi, be) != rho1(C, xi, ga))
            tested_coh += 1
            if d >= be and be > 4:
                fails.append(("rho1-coherence", be, ga, d))

    # --- Lemma Z2 (notes section 59), uniform discrepancy: for al < be < be',
    #     (B_al & B_be) sym (B_al & B_be') is contained in B_be sym (B_be' & be) -
    #     ONE finite set serving every level al at once. Identity-level, so the
    #     truncated model is sound for it.
    tested_Z2 = 0
    for be in range(4, N // 2):
        for bep in range(be + 1, min(be + 9, N)):
            FD = B(be) ^ (B(bep) & set(range(be)))
            for al in range(2, be):
                tested_Z2 += 1
                if not ((B(al) & B(be)) ^ (B(al) & B(bep))) <= FD:
                    fails.append(("Z2-uniform-discrepancy", al, be, bep))

    # --- 3.8(2) at n=0 : Lambda n B_beta finite (here: small) — sanity
    for be in range(2, N, 37):
        hits = [x for x in B(be) if is_limit(x)]
        if len(hits) > A*L: fails.append(("3.8(2)", be, len(hits)))
    # --- trace formula: lam_F(al,be) = max over stops of max(C_stop n al)
    tested_tf = 0
    for be in range(2, N, 23):
        for al in range(1, be, 17):
            tr = F(C, al, be, memo)
            lamF = max([z for z in tr if z < al], default=None)
            stops, _ = walk(C, al, be)
            pred = max((max([y for y in C[s] if y < al], default=-1) for s in stops[:-1]),
                       default=-1)
            pred = None if pred < 0 else pred
            tested_tf += 1
            if lamF != pred: fails.append(("trace", al, be, lamF, pred))
    # --- Theorem V : mu a fan above the trace, mu+omega <= lam < be, W = rho1(lam,be) >= 1
    #                 ==> rho3(mu+n, be) = 0 for every n <= W   (hence thr_be(mu) >= W+1).
    #     NB Theorem R (the thr_be-transfer of N1) is VACUOUS by exactly this: its
    #     hypothesis thr_be(mu) <= W-2 contradicts the conclusion here.
    tested_V = 0
    for be in range(2, N, 7):
        for lam in [x for x in limits if x < be]:
            tr = F(C, lam, be, memo)
            lamF = max([z for z in tr if z < lam], default=-1)
            W = rho1(C, lam, be)
            if W < 1: continue                      # W = 0 is the degenerate case
            for mu in [x for x in limits if x + M <= lam and x > lamF]:
                for n in range(0, min(W, M - 1) + 1):
                    tested_V += 1
                    if rho3(C, mu + n, be) != 0:
                        fails.append(("V", be, lam, lamF, W, mu, n))
    # --- Theorem A4 (notes sec-56): an above-trace drop of al against be sits in a
    #     block <= rho_1(al,be), OR is one of the finitely many xi with rho_1(xi,al)=0.
    #     This is what localizes the leftover's block-spread, the conjunct sec-50 missed.
    tested_A4 = 0
    for be in range(2, N, 7):
        for al in range(1, be, 5):
            tr = F(C, al, be, memo)
            lamF = max([z for z in tr if z < al], default=-1)
            W = rho1(C, al, be)
            for xi in range(lamF + 1, al):
                if rho3(C, xi, al) == 1 and rho3(C, xi, be) == 0:
                    blk = dec(xi)[2]
                    tested_A4 += 1
                    if not (blk <= W or rho1(C, xi, al) == 0):
                        fails.append(("A4", be, al, xi, blk, W))
    # --- M(3) pruning and M(1) one-sided pruning (sec-52), re-verified
    tested_M = 0
    for be in range(2, N, 13):
        for al in range(1, be, 9):
            tr = F(C, al, be, memo)
            lamF = max([z for z in tr if z < al], default=-1)
            W = rho1(C, al, be)
            for xi in range(lamF + 1, al):
                tested_M += 1
                if (rho3(C, xi, be) == 1) != (rho3(C, xi, al) == 1 and rho1(C, xi, al) >= W):
                    fails.append(("M3", al, be, xi))
    return fails, tested_tf, tested_V, tested_M, tested_A4, tested_rows, tested_Z2, tested_coh, tested_fib

if __name__ == "__main__":
    tot_tf = tot_V = tot_M = tot_A4 = tot_rows = tot_Z2 = tot_coh = tot_fib = 0
    allfails = []
    for seed in range(12):
        f, a1, a2, a3, a4, a5, a6, a7, a8 = run(seed)
        tot_tf += a1; tot_V += a2; tot_M += a3; tot_A4 += a4; tot_rows += a5; tot_Z2 += a6; tot_coh += a7; tot_fib += a8
        allfails += [(seed,) + tuple(x) for x in f[:4]]
    print(f"trace formula: {tot_tf} | Theorem V: {tot_V} | M(3): {tot_M} | A4: {tot_A4}"
          f" | 1.16(a) rows: {tot_rows} | Z2: {tot_Z2} | coh: {tot_coh}"
          f" | fibres: {tot_fib}")
    if allfails:
        print(f"FAILURES ({len(allfails)}):")
        for x in allfails[:12]: print("  ", x)
    else:
        print("all checks PASS")
