#!/usr/bin/env python3
"""
Experiments for the paper "Powers of Two in the Image of the Summatory Function
of 2^{v_2(k)}: On an Open Question of Nicolas".

Standalone: Python 3.12 (numpy optional), exact integer arithmetic only.

    c(n) = sum_{k=1}^{n} 2^{v_2(k)}
    A    = { a >= 0 : 2^a in c(N) }

Experiments E1-E8 check the statements of the paper; experiments E9-E16 compute the
successful states S_J = { w : (J, w) successful } of the recursion (Theorem 4.1) for
all J <= jmax and test conjectures on them.  E9-E16 use numpy if it is installed
(fast); without numpy they run in pure Python with jmax reduced to 8192.

Experiments E17-E19 check the forest structure (Theorem 8.4); experiments E20-E23 use the
bottom-up recursion (Theorem 8.6) up to level jmax2; E24 checks the symmetry families
(Theorem 8.7) and the counting bounds (Theorem 8.8); E25 treats c_p(n) = sum p^(v_p(k)) for odd
primes p (Section 9); E26 checks the immediate failures (Theorem 9.6) and E27 the bottom-up
recursion and symmetry for odd p (Theorem 9.7).  E28 counts the exponents of the three
families of Nicolas (Proposition 7.2).  E29 determines, for every prime, the exponents with
w_0 = 0 (accepted without any step of the recursion) and compares them with the exponents
of Theorem 9.5(1).  E30 evaluates the explicit lower bounds of Theorems 7.1 and 8.8 and
compares them with the numbers of family exponents and with A(x), B(x).

Usage (from any directory):
    python powers_of_two_c.py --xmax 20000                 # E1-E16, jmax = 2^16
    python powers_of_two_c.py --xmax 20000 --jmax 131072   # larger jmax (numpy)

Everything printed is also written to results_powers_of_two_c.txt next to this
script.  Each check prints PASS or FAIL; the summary at the end lists failures.
"""

import argparse
import math
import sys
import time
from pathlib import Path

try:
    import numpy as np
    HAVE_NP = True
except ImportError:
    HAVE_NP = False

OUT_LINES = []
FAILURES = []


def out(line=""):
    print(line, flush=True)
    OUT_LINES.append(line)


def check(name, ok, detail=""):
    status = "PASS" if ok else "FAIL"
    out(f"[{status}] {name}" + (f"  ({detail})" if detail else ""))
    if not ok:
        FAILURES.append(name)


# ---------------------------------------------------------------------------
# Basic functions
# ---------------------------------------------------------------------------

def c_formula(n):
    """Lemma 2.1: c(n) = n + (1/2) sum_{i in B(n)} i 2^i (exact integer form)."""
    s = 0
    m, i = n, 0
    while m:
        if m & 1:
            s += i << i
        m >>= 1
        i += 1
    assert s % 2 == 0
    return n + s // 2


def c_bits_form(n):
    """First form of Lemma 2.1: sum_{i in B(n)} 2^{i-1}(i+2), computed as (sum (i+2)2^i)/2."""
    s = 0
    m, i = n, 0
    while m:
        if m & 1:
            s += (i + 2) << i
        m >>= 1
        i += 1
    return s // 2


def ceil_log2(K):
    return (K - 1).bit_length()          # K >= 1


def beta(K):
    return K + ceil_log2(K)


def candidate_K(a):
    """Theorem 3.3: the unique K >= 2 with beta(K) = a + 3, or None."""
    b = a + 3
    K = max(2, b - b.bit_length() - 2)
    while beta(K) < b:
        K += 1
    return K if beta(K) == b else None


def is_skip(a):
    """a = 2^r + r - 2 for some r >= 1."""
    r = 1
    while (1 << r) + r - 2 <= a:
        if (1 << r) + r - 2 == a:
            return True
        r += 1
    return False


def least_s(J, w):
    """Least sigma >= 1 with 2^sigma w + sigma >= J + 1 (w >= 1)."""
    s = max(1, (J + 1).bit_length() - w.bit_length() - 1)
    while s > 1 and (w << (s - 1)) + (s - 1) >= J + 1:
        s -= 1
    while (w << s) + s < J + 1:
        s += 1
    return s


def membership(a, want_T=False):
    """
    Algorithm 1.  Returns dict with keys:
      member (bool), reason, K, h, steps, maxint, T (list, if want_T and member),
      fail_step (index of the iteration where failure occurred, 1-based, or 0).
    """
    K = candidate_K(a)
    if K is None:
        return {"member": False, "reason": "no K", "K": None, "h": None,
                "steps": 0, "maxint": 0, "T": None, "fail_step": 0}
    h = ceil_log2(K)
    J, w = K - 1, (1 << h) - K
    steps, maxint = 0, max(J, w)
    T = [K] if want_T else None
    while w >= 1:
        steps += 1
        s = least_s(J, w)
        val = (w << s) + s
        maxint = max(maxint, val)
        if (w << (s - 1)) + s == J + 1:
            return {"member": False, "reason": "failure", "K": K, "h": h,
                    "steps": steps, "maxint": maxint, "T": None, "fail_step": steps}
        if want_T:
            T.append(J + 1 - s)
        w = val - J - 1
        J = J - s
        maxint = max(maxint, J, w)
        assert J >= 1 and 0 <= w <= J - 1, (a, J, w)
    return {"member": True, "reason": "success", "K": K, "h": h,
            "steps": steps, "maxint": maxint, "T": T, "fail_step": 0}


def greedy_bigint(a):
    """Independent check with big integers: is 2^{a+3} a sum of distinct j 2^j?"""
    V = 1 << (a + 3)
    T = []
    j = a + 3
    while V and j >= 1:
        t = j << j
        if t <= V:
            V -= t
            T.append(j)
        j -= 1
    return V == 0, T


# ---------------------------------------------------------------------------
# Experiments
# ---------------------------------------------------------------------------

def exp_lemma(nmax):
    out(f"\n== E1. Lemma 2.1: c(n) by definition vs. both closed forms, 1 <= n <= {nmax} ==")
    t0 = time.time()
    c = 0
    bad = 0
    first_bad = None
    for n in range(1, nmax + 1):
        c += n & -n
        if c != c_formula(n) or c != c_bits_form(n):
            bad += 1
            if first_bad is None:
                first_bad = n
    check("Lemma 2.1 identity", bad == 0,
          f"{nmax} values, mismatches={bad}, first={first_bad}, {time.time()-t0:.1f}s")
    # c(2^r) = 2^{r-1}(r+2)
    ok = all(c_formula(1 << r) * 2 == (r + 2) << r for r in range(0, 200))
    check("c(2^r) = 2^{r-1}(r+2), 0 <= r < 200", ok)
    # table of Nicolas, Section 7
    table = [1, 3, 4, 8, 9, 11, 12, 20, 21, 23, 24, 28, 29, 31, 32, 48]
    ok = [c_formula(n) for n in range(1, 17)] == table
    check("c(1..16) equals the table of Nicolas (Section 7)", ok)


def exp_bruteforce(nmax_log):
    nmax = 1 << nmax_log
    out(f"\n== E2. Brute force: powers of 2 among c(1), ..., c(2^{nmax_log}) ==")
    t0 = time.time()
    c = 0
    found = {}
    for n in range(1, nmax + 1):
        c += n & -n
        if c & (c - 1) == 0:
            found[c.bit_length() - 1] = n
    cmax = c
    amax = cmax.bit_length() - 1       # every a <= amax has 2^a <= cmax
    out(f"c(2^{nmax_log}) = {cmax}; membership is exact for 0 <= a <= {amax}  ({time.time()-t0:.1f}s)")
    out("a : n with c(n)=2^a (brute force)")
    for a in range(0, amax + 1):
        out(f"  {a:3d} : {found.get(a, '-')}")
    # compare with Algorithm 1 and with the big-integer greedy
    ok_alg = ok_gr = ok_n = True
    for a in range(0, amax + 1):
        brute = a in found
        r = membership(a, want_T=True)
        g, T = greedy_bigint(a)
        ok_alg &= (r["member"] == brute)
        ok_gr &= (g == brute)
        if brute:
            n_alg = sum(1 << (j - 2) for j in r["T"])
            ok_n &= (n_alg == found[a])
    check(f"Algorithm 1 agrees with brute force for 0 <= a <= {amax}", ok_alg)
    check(f"big-integer greedy agrees with brute force for 0 <= a <= {amax}", ok_gr)
    check("Corollary 4.2: n = sum 2^{j-2} over T equals the brute-force n", ok_n)
    return found, amax


def exp_theorem_leading(bmax):
    out(f"\n== E3. Theorem 3.3: candidates K and missing values of beta, 3 <= b <= {bmax} ==")
    # beta strictly increasing, image complement = {2^r + r + 1}
    vals = set()
    K = 2
    while beta(K) <= bmax:
        assert beta(K + 1) > beta(K)
        vals.add(beta(K))
        K += 1
    missing = sorted(set(range(3, bmax + 1)) - vals)
    expected = []
    r = 1
    while (1 << r) + r + 1 <= bmax:
        expected.append((1 << r) + r + 1)
        r += 1
    check("beta strictly increasing; b >= 3 not in image = {2^r + r + 1}", missing == expected,
          f"missing={missing}")
    # 0 <= 2^h - K <= K - 2
    ok = True
    for K in range(2, 1 << 16):
        h = ceil_log2(K)
        ok &= 0 <= (1 << h) - K <= K - 2
    check("0 <= 2^h - K <= K - 2 for 2 <= K < 2^16", ok)


def exp_algorithm_vs_greedy(gmax):
    out(f"\n== E4. Algorithm 1 vs. big-integer greedy, 0 <= a <= {gmax} ==")
    t0 = time.time()
    bad = []
    nT_bad = 0
    for a in range(0, gmax + 1):
        r = membership(a, want_T=True)
        g, Tg = greedy_bigint(a)
        if r["member"] != g:
            bad.append(a)
        elif g:
            if sorted(r["T"], reverse=True) != Tg:
                nT_bad += 1
            elif a <= 1500:
                n = sum(1 << (j - 2) for j in r["T"])
                if c_formula(n) != 1 << a:
                    nT_bad += 1
    check("Algorithm 1 = greedy on all a", not bad, f"disagreements={bad[:10]}, {time.time()-t0:.1f}s")
    check("set T of Algorithm 1 = greedy set; c(n) = 2^a for a <= 1500", nT_bad == 0)


def exp_counting_table(xmax):
    out(f"\n== E5. A(x), B(x) and step statistics for 0 <= a <= {xmax} ==")
    t0 = time.time()
    nicolas = {1000: 635, 2000: 1374, 3000: 1787, 4000: 2405, 5000: 2748,
               6000: 3078, 7000: 3646, 8000: 4380, 9000: 5227, 10000: 5963}
    A = 0
    maxsteps = 0
    maxint_ratio = 0.0
    steps_bound_ok = True
    int_bound_ok = True
    fail_first = fail_later = skips = 0
    rows = []
    members = []
    results = {}
    for a in range(0, xmax + 1):
        r = membership(a)
        results[a] = r
        if r["K"] is not None:
            K = r["K"]
            steps_bound_ok &= r["steps"] <= max(0, K - 2)
            int_bound_ok &= r["maxint"] <= 2 * K
            maxsteps = max(maxsteps, r["steps"])
        if r["member"]:
            A += 1
            members.append(a)
        elif r["reason"] == "no K":
            skips += 1
        elif r["fail_step"] == 1:
            fail_first += 1
        else:
            fail_later += 1
        if a > 0 and a % 1000 == 0:
            rows.append((a, A, a + 1 - A))
    out(f"computed in {time.time()-t0:.1f}s")
    check("Corollary 4.2: number of iterations <= K - 2", steps_bound_ok)
    check("Corollary 4.2: integers handled in the loop <= 2K", int_bound_ok)
    # Nicolas's table counts the exponents 1 <= a <= x, i.e. A(x) - 1 (a = 0 is in A since c(1) = 2^0).
    out("     x      A(x)    B(x)    A(x)/x   A(x)-1   Nicolas")
    for x, Ax, Bx in rows:
        nic = nicolas.get(x, "")
        out(f"{x:7d} {Ax:8d} {Bx:7d}  {Ax/x:7.4f} {Ax-1:8d}   {nic}")
    check("0 in A (c(1) = 2^0)", results[0]["member"])
    agree = all(Ax - 1 == nicolas[x] for x, Ax, _ in rows if x in nicolas)
    check("A(x) - 1 (exponents 1 <= a <= x) agrees with the table of Nicolas (x = 1000, ..., 10000)", agree)
    # first-iteration failures vs. the families of Theorem 6.1
    first_fail = sorted(a for a, r in results.items() if r["fail_step"] == 1)
    fam = set()
    h = 1
    while (1 << (h - 1)) + h - 3 <= xmax:
        cases = [1 << i for i in range(1, h) if (h - i) % (2 * ((1 << i) - 1)) == 0]
        if h % 4 == 3:
            cases.append(3)
        for s in cases:
            K = ((1 << (h + s - 1)) + s) // ((1 << (s - 1)) + 1)
            if K + h - 3 <= xmax:
                fam.add(K + h - 3)
        h += 1
    out(f"exponents rejected at the first iteration: {first_fail}")
    check("first-iteration failures a <= xmax = exponents of Theorem 6.1 families a <= xmax",
          set(first_fail) == fam, f"{len(first_fail)} vs {len(fam)}")
    # Theorem 6.2 (1)-(2): members decided with 0 or 1 iteration vs. the families of Theorem 5.1
    zero = sorted(a for a, r in results.items() if r["member"] and r["steps"] == 0)
    one = sorted(a for a, r in results.items() if r["member"] and r["steps"] == 1)
    fam0, fam1 = set(), set()
    h = 1
    while (1 << (h - 1)) + h - 3 <= xmax:
        if (1 << h) + h - 3 <= xmax:
            fam0.add((1 << h) + h - 3)
        for k in range(0, h):
            s_ = 1 << k
            if h >= k + 2 and (h - k) % (1 << (k + 1)) == 0:
                K = ((1 << (h + s_)) + s_) // ((1 << s_) + 1)
                if K + h - 3 <= xmax:
                    fam1.add(K + h - 3)
        h += 1
    out(f"members decided without iteration: {zero}")
    out(f"members decided after exactly one iteration: {one}")
    check("members with 0 iterations = exponents of Theorem 5.1(1) <= xmax", set(zero) == fam0,
          f"{len(zero)} vs {len(fam0)}")
    check("members with exactly 1 iteration = exponents of Theorem 5.1(2) <= xmax", set(one) == fam1,
          f"{len(one)} vs {len(fam1)}")
    # distribution of the number of iterations
    hist = {}
    for a, r in results.items():
        if r["K"] is not None:
            key = (r["member"], min(r["steps"], 10))
            hist[key] = hist.get(key, 0) + 1
    out("number of iterations (10 means >= 10):  members / non-members")
    for st in range(0, 11):
        out(f"  {st:2d}: {hist.get((True, st), 0):7d} / {hist.get((False, st), 0):7d}")
    out(f"non-members up to {xmax}: no candidate K = {skips}, failure at first iteration = {fail_first}, "
        f"failure at a later iteration = {fail_later}")
    out(f"maximal number of iterations = {maxsteps}")
    # A(x) per dyadic block of K: proportion of successful candidates
    out("\nproportion of members among candidates K in (2^{h-1}, 2^h]:")
    out("   h   candidates   members   proportion")
    byh = {}
    for a in range(0, xmax + 1):
        K = results[a]["K"]
        if K is None:
            continue
        h = ceil_log2(K)
        if (1 << h) + h - 3 > xmax:
            continue          # block not complete
        tot, mem = byh.get(h, (0, 0))
        byh[h] = (tot + 1, mem + (1 if results[a]["member"] else 0))
    for h in sorted(byh):
        tot, mem = byh[h]
        out(f"{h:4d} {tot:11d} {mem:9d}   {mem/tot:8.4f}")
    return members


def exp_member_families(hmax_formula, hmax_alg, gmax):
    out(f"\n== E6. Theorem 5.1 (members): closed formula for h <= {hmax_formula}, "
        f"Algorithm 1 for h <= {hmax_alg} ==")
    ok1 = all(c_formula(1 << ((1 << r) - 2)) == 1 << ((1 << r) + r - 3) for r in range(1, 12))
    check("part (1): c(2^{2^r-2}) = 2^{2^r+r-3}, 1 <= r <= 11", ok1)
    ok_int = ok_range = ok_c = ok_alg = ok_gr = True
    count = 0
    listing = []
    for k in range(0, 12):
        s = 1 << k
        for h in range(k + 2, hmax_formula + 1):
            if (h - k) % (1 << (k + 1)):
                continue
            num = (1 << (h + s)) + s
            den = (1 << s) + 1
            ok_int &= num % den == 0
            K = num // den
            ok_range &= (1 << (h - 1)) < K < (1 << h) and K - s >= 2
            # identity behind (eq. member): K(2^s+1) - s = 2^{h+s}; direct c(n) when n is small
            ok_c &= K * ((1 << s) + 1) - s == 1 << (h + s)
            if h <= 16:
                ok_c &= c_formula((1 << (K - 2)) + (1 << (K - s - 2))) == 1 << (K + h - 3)
            a = K + h - 3
            if h <= hmax_alg:
                ok_alg &= membership(a)["member"]
                listing.append((k, s, h, K, a))
            if a <= gmax:
                ok_gr &= greedy_bigint(a)[0]
            count += 1
    check("K integer", ok_int, f"{count} pairs (k, h)")
    check("2^{h-1} < K < 2^h and K - s >= 2", ok_range)
    check("c(2^{K-2} + 2^{K-s-2}) = 2^{K+h-3}", ok_c)
    check(f"Algorithm 1 returns member (h <= {hmax_alg})", ok_alg)
    check(f"big-integer greedy returns member (a <= {gmax})", ok_gr)
    out("   k    s    h          K          a")
    for k, s, h, K, a in listing:
        out(f"{k:4d} {s:4d} {h:4d} {K:10d} {a:10d}")
    out(f"example: c(2^24 + 2^22) = 2^28 -> {c_formula((1 << 24) + (1 << 22)) == 1 << 28}")


def exp_nonmember_families(hmax_first, hmax_alg, gmax):
    out(f"\n== E7. Theorem 6.1 (non-members): first-iteration failure for h <= {hmax_first}, "
        f"Algorithm 1 for h <= {hmax_alg} ==")
    ok_int = ok_range = ok_first = ok_alg = ok_gr = True
    count = 0
    listing = []
    cases = [(1 << i, i) for i in range(1, 12)] + [(3, None)]
    for s, i in cases:
        for h in range(1, hmax_first + 1):
            if i is not None:
                if not (h > i and (h - i) % (2 * ((1 << i) - 1)) == 0):
                    continue
            else:
                if h % 4 != 3:
                    continue
            M = (1 << (s - 1)) + 1
            num = (1 << (h + s - 1)) + s
            ok_int &= num % M == 0
            K = num // M
            ok_range &= (1 << (h - 1)) < K < (1 << h)
            J, w = K - 1, (1 << h) - K
            st = least_s(J, w)
            ok_first &= (st == s) and ((w << (s - 1)) + s == J + 1)
            a = K + h - 3
            if h <= hmax_alg:
                r = membership(a)
                ok_alg &= (not r["member"]) and r["fail_step"] == 1
                listing.append((s, h, K, a))
            if a <= gmax:
                ok_gr &= not greedy_bigint(a)[0]
            count += 1
    check("K integer", ok_int, f"{count} pairs (s, h)")
    check("2^{h-1} < K < 2^h", ok_range)
    check("least s equals the family s and 2^{s-1}w + s = J + 1", ok_first)
    check(f"Algorithm 1 fails at the first iteration (h <= {hmax_alg})", ok_alg)
    check(f"big-integer greedy returns non-member (a <= {gmax})", ok_gr)
    out("   s    h          K          a")
    for s, h, K, a in listing:
        out(f"{s:4d} {h:4d} {K:10d} {a:10d}")
    ok_skip = all(candidate_K((1 << r) + r - 2) is None for r in range(1, 40))
    check("a = 2^r + r - 2 has no candidate K, 1 <= r < 40", ok_skip)
    # Nicolas's families
    ok_n1 = all(membership(a + ((1 << a) - 11) // 3)["member"] for a in range(3, 16, 2))
    ok_n2 = all(not membership(a + ((1 << a) - 10) // 3)["member"] for a in range(4, 16, 2))
    check("Nicolas: a + (2^a - 11)/3 in A for odd 3 <= a <= 15", ok_n1)
    check("Nicolas: a + (2^a - 10)/3 not in A for even 4 <= a <= 14", ok_n2)


def exp_counting_bounds(members_upto, xmax):
    out("\n== E8. Theorem 7.1: family counts vs. the explicit lower bounds ==")
    E = sum(1.0 / ((1 << i) - 1) for i in range(1, 200))
    out(f"E = {E:.12f},  5/4 + E/2 = {1.25 + E/2:.12f}")
    member_set = set(members_upto)
    out("        x    H   members(fam)   2H-log2H-3   A(x)   nonmem(fam)   B(x)")
    ok = True
    for x in [16, 64, 256, 1000, 4096, 10000, 65536, 10**6, 10**9, 10**12]:
        H = int(math.floor(math.log2(x))) - 1
        # member family exponents with h <= H
        mem = set()
        for h in range(1, H + 1):
            mem.add(beta(1 << h) - 3)
            for k in range(0, h):
                s = 1 << k
                if h >= k + 2 and (h - k) % (1 << (k + 1)) == 0:
                    K = ((1 << (h + s)) + s) // ((1 << s) + 1)
                    mem.add(K + h - 3)
        non = set((1 << r) + r - 2 for r in range(1, H + 1))
        for h in range(1, H + 1):
            fams = [(1 << i) for i in range(1, h) if (h - i) % (2 * ((1 << i) - 1)) == 0]
            if h % 4 == 3:
                fams.append(3)
            for s in fams:
                K = ((1 << (h + s - 1)) + s) // ((1 << (s - 1)) + 1)
                non.add(K + h - 3)
        ok &= max(mem) <= x and max(non) <= x and not (mem & non)
        bound = 2 * H - math.log2(H) - 3
        ok &= len(mem) >= bound
        if x <= xmax:
            Ax = sum(1 for a in member_set if a <= x)
            Bx = x + 1 - Ax
            ok &= mem <= member_set and not (non & member_set)
            out(f"{x:9d} {H:4d} {len(mem):13d} {bound:12.2f} {Ax:6d} {len(non):12d} {Bx:6d}")
        else:
            out(f"{x:13d} {H:4d} {len(mem):9d} {bound:12.2f}      - {len(non):12d}      -")
    check("family exponents are <= x, disjoint, members/non-members confirmed, member bound holds", ok)


# ---------------------------------------------------------------------------
# Successful states S_J (exploration)
# ---------------------------------------------------------------------------

def state_success(J, w):
    while w >= 1:
        s = least_s(J, w)
        if (w << (s - 1)) + s == J + 1:
            return False
        w = (w << s) + s - J - 1
        J -= s
    return True


def greedy_bigint_state(J, w):
    """Independent check: is 2^{J+1} w in E_J ?"""
    V = w << (J + 1)
    for j in range(J, 0, -1):
        t = j << j
        if t <= V:
            V -= t
    return V == 0


# ---------------------------------------------------------------- row computation

def row_python(J, rows):
    """Labels of the states at level J: J0 > 0 if the orbit ends at the root (J0, 0)
    (successful), -(Jf*64 + s) < 0 if it ends at the failing state of level Jf and step s."""
    r = [0] * J
    r[0] = J
    nfail = 0
    for w in range(1, J):
        s = least_s(J, w)
        if (w << (s - 1)) + s == J + 1:
            r[w] = -(J * 64 + s)
            nfail += 1
            continue
        wp = (w << s) + s - J - 1
        r[w] = rows[J - s][wp]
    return r, nfail


def row_numpy(J, rows, wv):
    """Same labels as row_python, vectorized.  wv = np.arange(jmax+1, dtype=int64)."""
    w = wv[1:J]
    # bit length of w (exact for w < 2^53)
    _, e = np.frexp(w.astype(np.float64))
    bl = e.astype(np.int64)
    s = np.maximum(1, (J + 1).bit_length() - bl - 1)
    # adjust down while s-1 also admissible, then up while s not admissible
    for _ in range(4):
        dn = (s > 1) & (((w << (s - 1)) + (s - 1)) >= J + 1)
        if not dn.any():
            break
        s = s - dn
    for _ in range(6):
        up = ((w << s) + s) < J + 1
        if not up.any():
            break
        s = s + up
    assert not (((w << s) + s) < J + 1).any()
    assert not ((s > 1) & (((w << (s - 1)) + (s - 1)) >= J + 1)).any()
    fail = ((w << (s - 1)) + s) == J + 1
    wp = (w << s) + s - J - 1
    res = np.zeros(J, dtype=np.int64)
    res[0] = J
    res[1:][fail] = -(J * 64 + s[fail])
    ok = ~fail
    for sv in np.unique(s[ok]):
        m = ok & (s == sv)
        res[1:][m] = rows[J - int(sv)][wp[m]]
    return res, int(fail.sum())


def tree_stats(J, lab, use_np):
    """Number of distinct trees among the states of level J and the 10 largest."""
    if use_np:
        u, c = np.unique(lab, return_counts=True)
        order = np.argsort(-c, kind="stable")[:10]
        top = [(int(u[k]), int(c[k])) for k in order]
        ntrees = len(u)
    else:
        from collections import Counter
        cnt = Counter(lab)
        top = cnt.most_common(10)
        ntrees = len(cnt)
    return ntrees, top


def compute(jmax, use_np):
    keep = jmax.bit_length() + 3
    rows = {}
    N = [0] * (jmax + 1)
    F = [0] * (jmax + 1)          # number of failing states at level J
    sym_ok = True
    first_rows = {}
    block_member = {}      # h -> list of (K, member)
    checkpoints = set((1 << m) for m in range(5, jmax.bit_length())) | {jmax}
    trees = {}             # J -> (ntrees, top10)
    wv = np.arange(jmax + 1, dtype=np.int64) if use_np else None
    t0 = time.time()
    for J in range(1, jmax + 1):
        if use_np:
            lab, nf = row_numpy(J, rows, wv)
            rb = lab > 0
            Nj = int(rb.sum())
            if not np.array_equal(rb, rb[::-1]):
                sym_ok = False
        else:
            lab, nf = row_python(J, rows)
            rb = [1 if x > 0 else 0 for x in lab]
            Nj = sum(rb)
            if rb != rb[::-1]:
                sym_ok = False
        rows[J] = lab
        N[J] = Nj
        F[J] = nf
        if J in checkpoints:
            trees[J] = tree_stats(J, lab, use_np)
        if J <= 64:
            first_rows[J] = "".join("1" if x else "0" for x in (rb.tolist() if use_np else rb))
        # initial state of K = J + 1
        K = J + 1
        h = ceil_log2(K)
        w0 = (1 << h) - K
        block_member.setdefault(h, []).append((K, bool(rb[w0])))
        rows.pop(J - keep, None)
        if J % 8192 == 0:
            out(f"  J = {J}  ({time.time()-t0:.0f}s)")
    return N, sym_ok, first_rows, block_member, time.time() - t0, F, trees


# ---------------------------------------------------------------- main


def exp_states(jmax, use_np):
    out(f"\n== Successful states S_J for J <= {jmax} (numpy={'yes ' + np.__version__ if use_np else 'no'}) ==")
    N, sym_ok, first_rows, block_member, dt, F, trees = compute(jmax, use_np)
    out(f"rows computed in {dt:.1f}s")

    # X1: validation against Algorithm 1 and the big-integer greedy
    out("\n== E9. Validation of the row computation ==")
    import random
    rnd = random.Random(12345)
    bad1 = bad2 = 0
    # recompute a few rows exactly with the reference functions
    for J in list(range(1, min(200, jmax + 1))) + [rnd.randrange(200, min(1500, jmax) + 1) for _ in range(10) if jmax >= 200]:
        Nref = sum(1 for w in range(J) if state_success(J, w))
        if Nref != N[J]:
            bad1 += 1
    for J in range(1, 120):
        for w in range(J):
            if state_success(J, w) != greedy_bigint_state(J, w):
                bad2 += 1
    check("N(J) from rows = N(J) from Algorithm 1 (J < 200 and 10 random J in [200, 1500])", bad1 == 0, f"mismatches={bad1}")
    check("Algorithm 1 = big-integer greedy on all states with J < 120", bad2 == 0, f"mismatches={bad2}")

    # X2: symmetry  w <-> J-1-w  (proved: complement in {2..J})
    out("\n== E10. Symmetry of S_J under w -> J-1-w ==")
    check(f"S_J symmetric for all J <= {jmax}", sym_ok)

    # X3: S_J for small J and N(J)
    out("\n== E11. S_J as bit strings (w = 0..J-1) and N(J), J <= 64 ==")
    for J in range(1, 65):
        out(f"{J:3d} N={N[J]:3d}  {first_rows[J]}")

    # X4: N(J)/J statistics on dyadic ranges
    out("\n== E12. N(J)/J on dyadic ranges [2^m, 2^{m+1}) ==")
    out("   m     min N/J    J_min     max N/J    J_max    mean N/J   N(J)=J count  N power of 2 count")
    m = 0
    while (1 << m) <= jmax:
        lo, hi = 1 << m, min((1 << (m + 1)) - 1, jmax)
        vals = [(N[J] / J, J) for J in range(lo, hi + 1)]
        mn = min(vals)
        mx = max(vals)
        mean = sum(v for v, _ in vals) / len(vals)
        full = sum(1 for J in range(lo, hi + 1) if N[J] == J)
        pw = sum(1 for J in range(lo, hi + 1) if N[J] & (N[J] - 1) == 0)
        out(f"{m:4d} {mn[0]:10.4f} {mn[1]:8d} {mx[0]:10.4f} {mx[1]:8d} {mean:10.4f} {full:12d} {pw:12d}")
        m += 1
    out("J with N(J) = J (every state successful), J <= jmax:")
    out("  " + str([J for J in range(1, jmax + 1) if N[J] == J][:200]))

    # X5: predecessor identity  N(J) = 1 + sum_s #{w' in S_{J-s} : 2^s | w' + J - s + 1}
    # (checked indirectly through X1); print N(J) around powers of two
    out("\n== E13. N(J) near powers of two ==")
    for m in range(2, jmax.bit_length()):
        P = 1 << m
        seg = [(J, N[J]) for J in range(max(1, P - 3), min(jmax, P + 4) + 1)]
        out(f"  2^{m}: " + ", ".join(f"N({J})={n}" for J, n in seg))

    # X6: members per block, compared with the density of S_J
    out("\n== E14. Members among candidates K in (2^{h-1}, 2^h] (initial states) vs. mean N(J)/J ==")
    out("   h   candidates   members  proportion   mean N(J)/J on the block")
    for h in sorted(block_member):
        lst = block_member[h]
        if len(lst) != (1 << (h - 1)):
            continue   # block not complete
        mem = sum(1 for _, b in lst if b)
        Js = [K - 1 for K, _ in lst]
        dens = sum(N[J] / J for J in Js if J >= 1) / len(Js)
        out(f"{h:4d} {len(lst):11d} {mem:9d}  {mem/len(lst):10.4f}   {dens:10.4f}")

    # X7: profile of members inside a block (8 equal sub-intervals of K)
    out("\n== E15. Proportion of members in 8 equal sub-intervals of each block ==")
    for h in sorted(block_member):
        lst = block_member[h]
        if h < 6 or len(lst) != (1 << (h - 1)):
            continue
        L = len(lst)
        parts = []
        for q in range(8):
            sub = lst[q * L // 8:(q + 1) * L // 8]
            parts.append(sum(b for _, b in sub) / len(sub))
        out(f"  h={h:2d}: " + " ".join(f"{p:.3f}" for p in parts))

    # X8: A(x) for larger x
    out("\n== E16. A(x) for x up to beta(Jmax+1) - 3 ==")
    members = []
    for h in sorted(block_member):
        for K, b in block_member[h]:
            if b:
                members.append(K + ceil_log2(K) - 3)
    members.sort()
    xmax = (jmax + 1) + ceil_log2(jmax + 1) - 3
    # a <= xmax all have candidate K <= jmax + 1
    xs = [x for x in [1000 * i for i in range(1, 1000)] if x <= xmax]
    step = max(1, len(xs) // 40)
    import bisect
    out("        x       A(x)    A(x)/x")
    for x in xs[::step] + ([xs[-1]] if xs and xs[-1] not in xs[::step] else []):
        Ax = bisect.bisect_right(members, x)
        out(f"{x:9d} {Ax:10d} {Ax/x:9.4f}")
    if xs:
        ratios = [bisect.bisect_right(members, x) / x for x in xs]
        out(f"A(x)/x over x = 1000, 2000, ..., {xs[-1]}: min {min(ratios):.4f}, max {max(ratios):.4f}")
    # consistency with the earlier run
    Ax20 = bisect.bisect_right(members, 20000) if xmax >= 20000 else None
    if Ax20 is not None:
        check("A(20000) = 14836 (E5)", Ax20 == 14836, f"A(20000)={Ax20}")
    return N, sym_ok, first_rows, block_member, dt, F, trees


def phi(J, w):
    """The map of Theorem 4.1 on a state with w >= 1: returns (J', w') or None if it fails."""
    s = least_s(J, w)
    if (w << (s - 1)) + s == J + 1:
        return None
    return J - s, (w << s) + s - J - 1


def v2(n):
    return (n & -n).bit_length() - 1


def exp_forest(jmax, res):
    out(f"\n== Forest structure of the states, J <= {jmax} ==")
    N, sym_ok, first_rows, block_member, dt, F, trees = res

    # E17: failing states, formula of part (1)
    out("\n== E17. Failing states: F(J) = #{s >= 2 : 2^{s-1} | J+1-s, J+1-s >= 2^{s-1}} ==")
    bad = 0
    for J in range(1, jmax + 1):
        f = sum(1 for s in range(2, J.bit_length() + 2) if (J + 1 - s) >= (1 << (s - 1)) and (J + 1 - s) % (1 << (s - 1)) == 0)
        if f != F[J]:
            bad += 1
    check(f"F(J) from the rows = formula, J <= {jmax}", bad == 0, f"mismatches={bad}")
    ok = True
    for L in [10, 100, 1000, 10000, jmax]:
        if L > jmax:
            continue
        lhs = sum(F[1:L + 1])
        rhs = sum((L + 1 - s) >> (s - 1) for s in range(2, L + 1))
        ok &= lhs == rhs
        out(f"  L = {L:6d}: sum F(J) = {lhs:6d},  sum_s floor((L+1-s)/2^(s-1)) = {rhs:6d}")
    check("sum_{J<=L} F(J) = sum_{s>=2} floor((L+1-s)/2^{s-1})", ok)
    out(f"max F(J), J <= {jmax}: {max(F[1:])}")

    # E18: preimages, part (2)
    L = 600
    out(f"\n== E18. Preimages: every state (J', w') with J' <= {L} has exactly v2(J'+1+w') preimages ==")
    cnt = {}
    for J in range(2, L + 14):
        for w in range(1, J):
            r = phi(J, w)
            if r is not None:
                cnt[r] = cnt.get(r, 0) + 1
    bad = 0
    for Jp in range(1, L + 1):
        for wp in range(Jp):
            if cnt.get((Jp, wp), 0) != v2(Jp + 1 + wp):
                bad += 1
    check(f"number of preimages = v2(J'+1+w') for all states with J' <= {L}", bad == 0, f"mismatches={bad}")
    # N(J) recursion of part (3)
    bad = 0
    Srows, labrows = {}, {}
    for J in range(1, 1201):
        lab, _ = row_python(J, labrows)
        labrows[J] = lab
        Srows[J] = [w for w in range(J) if lab[w] > 0]
    for J in range(2, 1201):
        # only s with 2^s <= 2(J-s) can contribute, since J-s+1+w' <= 2(J-s)
        rhs = 1 + sum(1 for s in range(1, min(J, 13)) for wp in Srows[J - s] if (J - s + 1 + wp) % (1 << s) == 0)
        if rhs != len(Srows[J]):
            bad += 1
    check("N(J) = 1 + sum_s #{w' in S_{J-s} : 2^s | J-s+1+w'}, J <= 1200", bad == 0, f"mismatches={bad}")

    # E19: trees at levels 2^m
    out("\n== E19. Trees of the forest at levels J = 2^m and J = jmax ==")
    out("  labels: S@J0 = successful tree with root (J0, 0); F@Jf,s = failing state of level Jf and step s")
    def name(code):
        return f"S@{code}" if code > 0 else f"F@{(-code) >> 6},{(-code) & 63}"
    out("       J   trees   N(J)/J   largest   share   top5 share   top10 share")
    for J in sorted(trees):
        nt, top = trees[J]
        c1 = top[0][1] / J
        c5 = sum(c for _, c in top[:5]) / J
        c10 = sum(c for _, c in top[:10]) / J
        out(f"{J:8d} {nt:7d}  {N[J]/J:7.4f}   {name(top[0][0]):>12s}  {c1:6.4f}   {c5:9.4f}   {c10:10.4f}")
    Jl = max(trees)
    out(f"  the 10 largest trees at level J = {Jl}:")
    for code, c in trees[Jl][1]:
        out(f"    {name(code):>14s}  {c:7d} states  ({c/Jl:.4f})")


def bottomup_next(prev, J, use_np):
    """Theorem 8.6: S_J from S_{J-1} (indicator arrays of length J-1 and J)."""
    if use_np:
        new = np.zeros(J, dtype=bool)
        if J % 2:
            ev = np.arange(0, J - 1, 2)
            od = np.arange(1, J - 1, 2)
            new[ev // 2] = prev[ev]
            new[(od + J) // 2] = prev[od]
        else:
            half = J // 2
            new[:half] = prev[0::2]
            new[half:] = prev[0::2]
        return new
    new = [False] * J
    for c in range(J - 1):
        if not prev[c]:
            continue
        if J % 2:
            new[c // 2 if c % 2 == 0 else (c + J) // 2] = True
        elif c % 2 == 0:
            new[c // 2] = True
            new[c // 2 + J // 2] = True
    return new


def exp_bottomup(jmax2, res, use_np):
    out(f"\n== Bottom-up recursion (Theorem 8.6) for J <= {jmax2} ==")
    N_td, sym_ok, first_rows, block_member, dt, F, trees = res
    jmax = len(N_td) - 1
    # E20: rows equal to the top-down rows (full rows for J <= 3000, N(J) and members for J <= jmax)
    labrows = {}
    prev = np.ones(1, dtype=bool) if use_np else [True]       # S_1 = {0}
    bad_rows = bad_N = bad_mem = 0
    per_ok = True
    sym2_ok = True
    N = [0, 1]
    blk = {1: [(2, True)]}  # K = 2 has initial state (1, 0)
    t0 = time.time()
    for J in range(2, jmax2 + 1):
        cur = bottomup_next(prev, J, use_np)
        nJ = int(cur.sum()) if use_np else sum(cur)
        N.append(nJ)
        if J % 2 == 0:
            half = J // 2
            if use_np:
                per_ok &= bool(np.array_equal(cur[:half], cur[half:]))
            else:
                per_ok &= cur[:half] == cur[half:]
        if use_np:
            sym2_ok &= bool(np.array_equal(cur, cur[::-1]))
        else:
            sym2_ok &= cur == cur[::-1]
        if J <= jmax and nJ != N_td[J]:
            bad_N += 1
        K = J + 1
        h = ceil_log2(K)
        mem = bool(cur[(1 << h) - K])
        blk.setdefault(h, []).append((K, mem))
        prev = cur
        if J % 65536 == 0:
            out(f"  J = {J}  ({time.time()-t0:.0f}s)")
    out(f"bottom-up rows computed in {time.time()-t0:.1f}s")
    # full rows for small J against row_python labels
    labrows = {}
    prev = [True]
    for J in range(1, 3001):
        lab, _ = row_python(J, labrows)
        labrows[J] = lab
        if J >= 2:
            prev = bottomup_next(prev, J, False)
            if [x > 0 for x in lab] != prev:
                bad_rows += 1
    for h, lst in block_member.items():
        if h in blk and len(blk[h]) == len(lst):
            bad_mem += sum(1 for (K1, m1), (K2, m2) in zip(lst, blk[h]) if K1 != K2 or m1 != m2)
    out("\n== E20. Bottom-up recursion vs. the top-down rows ==")
    check("S_J bottom-up = S_J top-down (whole rows), J <= 3000", bad_rows == 0, f"mismatches={bad_rows}")
    check(f"N(J) bottom-up = N(J) top-down, J <= {jmax}", bad_N == 0, f"mismatches={bad_N}")
    check(f"membership of the initial states: bottom-up = top-down, blocks h with K <= {jmax + 1}", bad_mem == 0,
          f"mismatches={bad_mem}")
    out("\n== E21. Periodicity and symmetry ==")
    check(f"S_J has period J/2 for every even J <= {jmax2}", per_ok)
    check(f"S_J symmetric for every J <= {jmax2}", sym2_ok)
    check(f"N(2k+1) = N(2k) for 2k+1 <= {jmax2}", all(N[2 * k + 1] == N[2 * k] for k in range(1, (jmax2 - 1) // 2 + 1)))
    check(f"4 | N(J) for 4 <= J <= {jmax2}", all(N[J] % 4 == 0 for J in range(4, jmax2 + 1)))

    out("\n== E22. Members per block and N(J)/J, up to h = %d ==" % (jmax2 + 1).bit_length())
    out("   h   candidates   members  proportion   mean N(J)/J on the block")
    for h in sorted(blk):
        lst = blk[h]
        if len(lst) != (1 << (h - 1)):
            continue
        mem = sum(1 for _, b in lst if b)
        dens = sum(N[K - 1] / (K - 1) for K, _ in lst) / len(lst)
        out(f"{h:4d} {len(lst):11d} {mem:9d}  {mem/len(lst):10.4f}   {dens:10.4f}")
    out("\n   m     min N/J    J_min     max N/J    J_max    mean N/J")
    m = 0
    while (1 << (m + 1)) - 1 <= jmax2:
        lo, hi = 1 << m, (1 << (m + 1)) - 1
        vals = [(N[J] / J, J) for J in range(lo, hi + 1)]
        mn, mx = min(vals), max(vals)
        mean = sum(v for v, _ in vals) / len(vals)
        out(f"{m:4d} {mn[0]:10.4f} {mn[1]:8d} {mx[0]:10.4f} {mx[1]:8d} {mean:10.4f}")
        m += 1

    out("\n== E23. A(x) up to beta(jmax2 + 1) - 3 ==")
    import bisect
    members = sorted(K + ceil_log2(K) - 3 for h in blk for K, b in blk[h] if b)
    xmax2 = (jmax2 + 1) + ceil_log2(jmax2 + 1) - 3
    xs = [x for x in range(5000, xmax2 + 1, 5000)]
    out("        x       A(x)    A(x)/x")
    ratios = []
    for x in xs:
        Ax = bisect.bisect_right(members, x)
        ratios.append((Ax / x, x))
        out(f"{x:9d} {Ax:10d} {Ax/x:9.4f}")
    allr = [(bisect.bisect_right(members, x) / x, x) for x in range(1000, xmax2 + 1, 1000)]
    out(f"A(x)/x over x = 1000, 2000, ..., {allr[-1][1]}: min {min(allr)[0]:.4f} at x = {min(allr)[1]}, "
        f"max {max(allr)[0]:.4f} at x = {max(allr)[1]}")
    a65 = bisect.bisect_right(members, 65000)
    check("A(65000) = 56153 (E16)", a65 == 56153, f"A(65000)={a65}")

    # E24: families of Theorem 8.7 (symmetry families) and Theorem 8.8 (counting)
    out("\n== E24. Symmetry families (Theorem 8.7) ==")
    memset = set(members)
    C1 = sum(1.0 / ((1 << k) + 2) for k in range(0, 200))
    C2 = sum(1.0 / ((1 << k) + 1) for k in range(1, 200))
    E = sum(1.0 / ((1 << i) - 1) for i in range(1, 200))
    out(f"C1 = {C1:.12f}, C2 = {C2:.12f}, 3 + C1 = {3 + C1:.12f}, 5/4 + E/2 + C2 = {1.25 + E/2 + C2:.12f}")

    def fam1(H):
        return {(1 << (h - 1)) + 1: h for h in range(1, H + 1)}

    def fam2(h):
        res = []
        i = 1
        while True:
            sg = (1 << (i - 1)) + 1
            if h < sg + 2:
                break
            if (h - i) % (sg + 1) == 0:
                M = (1 << (sg + 1)) - 1
                num = (1 << h) - 2 * sg + 2
                res.append((i, sg, num, M))
            i += 1
        return res

    def fam3(h):
        res = []
        i = 2
        while True:
            sg = (1 << (i - 1)) + 1
            if h < sg + 1:
                break
            if (h - i) % sg == 0:
                M = (1 << sg) - 1
                num = (1 << h) - 2 * sg + 2
                res.append((i, sg, num, M))
            i += 1
        return res

    ok_c = all(c_formula((1 << (1 << r)) - 1) == 1 << ((1 << r) + r - 1) for r in range(0, 13))
    check("part (1): c(2^{2^r} - 1) = 2^{2^r + r - 1}, 0 <= r <= 12", ok_c)
    ok_int = ok_rng = True
    n2 = n3 = 0
    mem_ok = non_ok = gr_ok = True
    listing = []
    for h in range(1, 301):
        for kind, fam in (("member", fam2(h)), ("non-member", fam3(h))):
            for i, sg, num, M in fam:
                ok_int &= num % M == 0 and (num // M) % 2 == 0 and num // M >= 1
                w = num // M
                K = (1 << (h - 1)) + 1 + w // 2
                ok_rng &= (1 << (h - 1)) + 1 < K < (1 << h)
                a = K + h - 3
                if kind == "member":
                    n2 += 1
                    if a <= xmax2:
                        mem_ok &= a in memset
                    if a <= 4000:
                        gr_ok &= greedy_bigint(a)[0]
                else:
                    n3 += 1
                    if a <= xmax2:
                        non_ok &= a not in memset
                    if a <= 4000:
                        gr_ok &= not greedy_bigint(a)[0]
                if a <= xmax2:
                    listing.append((kind, i, sg, h, K, a))
    for h in range(1, 18):
        a = (1 << (h - 1)) + 1 + h - 3
        if a <= xmax2:
            mem_ok &= a in memset
    check("parts (2), (3): w is an even positive integer (h <= 300)", ok_int, f"{n2} member pairs, {n3} non-member pairs")
    check("parts (2), (3): 2^{h-1} + 1 < K < 2^h (h <= 300)", ok_rng)
    check(f"part (1) and (2) exponents <= {xmax2} are in A (bottom-up)", mem_ok)
    check(f"part (3) exponents <= {xmax2} are not in A (bottom-up)", non_ok)
    check("parts (2), (3) agree with the big-integer greedy (a <= 4000)", gr_ok)
    out("  kind         i   sigma    h          K          a")
    for kind, i, sg, h, K, a in listing:
        out(f"  {kind:11s} {i:2d} {sg:6d} {h:4d} {K:10d} {a:10d}")

    # Theorem 8.8: all families together, distinct, and counts
    out("\n  all families (Theorems 5.1, 6.1, 8.7 and the exponents 2^r + r - 2):")
    out("        x    H   members(fam)  (3+C1)H   A(x)   nonmem(fam)  (5/4+E/2+C2)H   B(x)")
    okd = True
    for x in [1000, 10000, 100000, 10**6, 10**9, 10**12]:
        H = int(math.floor(math.log2(x))) - 1
        memK, nonK = [], []
        for h in range(1, H + 1):
            memK.append((h, 1 << h))
            if h >= 3:
                memK.append((h, (1 << (h - 1)) + 1))
            for k in range(0, h):
                s_ = 1 << k
                if h >= k + 2 and (h - k) % (1 << (k + 1)) == 0:
                    memK.append((h, ((1 << (h + s_)) + s_) // ((1 << s_) + 1)))
            for _, sg, num, M in fam2(h):
                memK.append((h, (1 << (h - 1)) + 1 + (num // M) // 2))
            fams = [(1 << i) for i in range(1, h) if (h - i) % (2 * ((1 << i) - 1)) == 0]
            if h % 4 == 3:
                fams.append(3)
            for s_ in fams:
                nonK.append((h, ((1 << (h + s_ - 1)) + s_) // ((1 << (s_ - 1)) + 1)))
            for _, sg, num, M in fam3(h):
                nonK.append((h, (1 << (h - 1)) + 1 + (num // M) // 2))
        mem = set(K + ceil_log2(K) - 3 for _, K in memK)
        non = set(K + ceil_log2(K) - 3 for _, K in nonK) | set((1 << r) + r - 2 for r in range(1, H + 1))
        okd &= not (mem & non) and max(mem) <= x and max(non) <= x
        if x <= xmax2:
            okd &= mem <= memset and not (non & memset)
            Ax = bisect.bisect_right(members, x)
            out(f"{x:13d} {H:4d} {len(mem):9d} {(3 + C1) * H:10.2f} {Ax:7d} {len(non):10d} {(1.25 + E/2 + C2) * H:12.2f} {x + 1 - Ax:7d}")
        else:
            out(f"{x:13d} {H:4d} {len(mem):9d} {(3 + C1) * H:10.2f}       - {len(non):10d} {(1.25 + E/2 + C2) * H:12.2f}       -")
    check("all family exponents <= x, members and non-members disjoint and confirmed where computed", okd)


# ---------------------------------------------------------------------------
# An arbitrary prime p (Section "The analogue for an arbitrary prime")
# ---------------------------------------------------------------------------

def vp(n, p):
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def cp_formula(n, p):
    """Lemma: c_p(n) = sum d_i p^{i-1} ((p-1) i + p) over the base-p digits of n."""
    s, i = 0, 0
    while n:
        d = n % p
        if d:
            s += d * ((p - 1) * i + p) * p ** i
        n //= p
        i += 1
    assert s % p == 0
    return s // p


def g_of(K, p):
    """Least g >= 1 with p^g >= (p-1)(K+1) + 1."""
    g, t = 1, p
    while t < (p - 1) * (K + 1) + 1:
        t *= p
        g += 1
    return g


def candidate_p(a, p):
    b = a + 1
    K = max(0, b - b.bit_length() - 3)
    while K + g_of(K, p) < b:
        K += 1
    return K if K + g_of(K, p) == b else None


def skip_exponents_p(p, amax):
    res, g = [], 1
    while (p ** g - 1) // (p - 1) + g - 1 <= amax:
        res.append((p ** g - 1) // (p - 1) + g - 1)
        g += 1
    return res


def membership_p(a, p):
    """Theorem (recursion for p): returns (member, reason, steps)."""
    K = candidate_p(a, p)
    if K is None:
        return False, "no K", 0
    g = a + 1 - K
    u = (p - 1) * K + p
    d = p ** g // u
    assert 1 <= d <= p - 1
    w = p ** g - d * u
    if w > (p - 1) * K:
        return False, "immediate", 0
    steps = 0
    while w >= 1:
        steps += 1
        s = 1
        while p ** s * w < (p - 1) * (K - s) + p:
            s += 1
        i = K - s
        ui = (p - 1) * i + p
        d = p ** s * w // ui
        if d > p - 1:
            return False, "digit", steps
        w = p ** s * w - d * ui
        if w > (p - 1) * i:
            return False, "overflow", steps
        K = i
    return True, "success", steps


def greedy_p(a, p):
    V = p ** (a + 1)
    for i in range(a + 1, -1, -1):
        t = p ** i * ((p - 1) * i + p)
        d = min(V // t, p - 1)
        V -= d * t
    return V == 0


def exp_primes(primes, pxmax):
    out(f"\n== E25. Arbitrary primes p in {primes}: c_p(n) = sum p^(v_p(k)) ==")
    for p in primes:
        out(f"\n  --- p = {p} ---")
        # Lemma: digit formula and c_p(pn) = p c_p(n) + (p-1) n, by the definition
        N = 200000
        c, ok_f, cs = 0, True, [0]
        for n in range(1, N + 1):
            c += p ** vp(n, p)
            cs.append(c)
            if n <= 50000 and c != cp_formula(n, p):
                ok_f = False
        ok_r = all(cs[p * n] == p * cs[n] + (p - 1) * n for n in range(1, N // p + 1))
        check(f"p={p}: digit formula of c_p(n), n <= 50000", ok_f)
        check(f"p={p}: c_p(pn) = p c_p(n) + (p-1) n, pn <= {N}", ok_r)
        # Proposition: exponent of 1 - X in prod (1 - X^k) over F_p, n <= 30
        poly = [1]
        ok_fp = True
        for n in range(1, 31):
            newp = poly + [0] * n
            for j in range(len(poly)):
                newp[j + n] = (newp[j + n] - poly[j]) % p
            poly = newp
            P, e = poly[:], 0
            while sum(P) % p == 0:
                # divide by (1 - X): P = (1 - X) Q  <=>  Q_j = sum_{i<=j} P_i
                Q, acc = [], 0
                for coef in P[:-1]:
                    acc = (acc + coef) % p
                    Q.append(acc)
                P = Q
                e += 1
            ok_fp &= e == cs[n]
        check(f"p={p}: c_p(n) = exponent of 1-X in prod(1-X^k) over F_p, n <= 30", ok_fp)
        # brute force membership
        found = {}
        for n in range(1, N + 1):
            x = cs[n]
            while x % p == 0:
                x //= p
            if x == 1:
                e = 0
                y = cs[n]
                while y > 1:
                    y //= p
                    e += 1
                found[e] = n
        amax_b = 0
        while p ** (amax_b + 1) <= cs[N]:
            amax_b += 1
        ok1 = all(membership_p(a, p)[0] == (a in found) for a in range(amax_b + 1))
        ok2 = all(greedy_p(a, p) == (a in found) for a in range(amax_b + 1))
        out(f"  brute force over n <= {N}: exact for a <= {amax_b}; members: "
            + ", ".join(f"{a} (n={found[a]})" for a in sorted(found)))
        check(f"p={p}: recursion = brute force, a <= {amax_b}", ok1)
        check(f"p={p}: big-integer greedy = brute force, a <= {amax_b}", ok2)
        ok3 = all(membership_p(a, p)[0] == greedy_p(a, p) for a in range(0, 1201))
        check(f"p={p}: recursion = big-integer greedy, a <= 1200", ok3)
        # Theorem: candidates and skipped exponents
        sk = set(skip_exponents_p(p, 20000))
        ok4 = all((candidate_p(a, p) is None) == (a in sk) for a in range(0, 20001))
        check(f"p={p}: exponents without candidate = (p^g-1)/(p-1)+g-1, a <= 20000", ok4, f"{sorted(sk)}")
        # families
        okF1 = all(cp_formula(p ** ((p ** g - p) // (p - 1)), p) == p ** ((p ** g - p) // (p - 1) + g - 1)
                   for g in range(1, 6 if p == 3 else 4))
        okF1b = all(membership_p((p ** g - p) // (p - 1) + g - 1, p)[0] for g in range(1, 9 if p == 3 else 6))
        okF2 = all(not is_power(cp_formula(p ** m - 1, p), p) for m in range(1, 200))
        fam3 = []
        for g in range(2, 14 if p == 3 else 8, 2):
            K = (p ** g - 2 * p + 1) // (2 * (p - 1))
            fam3.append((g, K, K + g - 1, membership_p(K + g - 1, p)))
        okF3 = all(r[0] is False and r[1] == "immediate" and candidate_p(a, p) == K for g, K, a, r in fam3)
        check(f"p={p}: family (1) c_p(p^K) = p^(K+g-1) and members", okF1 and okF1b)
        check(f"p={p}: family (2) c_p(p^m - 1) not a power of p, m < 200", okF2)
        check(f"p={p}: family (3) immediate failures", okF3, ", ".join(f"g={g}: a={a}" for g, K, a, r in fam3))
        # counting function
        t0 = time.time()
        allres = {a: membership_p(a, p) for a in range(0, pxmax + 1)}
        mem = [a for a in range(0, pxmax + 1) if allres[a][0]]
        reasons = {}
        for a in range(0, pxmax + 1):
            r = allres[a]
            reasons[r[1]] = reasons.get(r[1], 0) + 1
        out(f"  A_p(x) for x <= {pxmax} computed in {time.time()-t0:.1f}s; outcomes: {reasons}")
        import bisect
        out("        x     A_p(x)   A_p(x)/x")
        step = max(500, pxmax // 12)
        for x in range(step, pxmax + 1, step):
            Ax = bisect.bisect_right(mem, x)
            out(f"  {x:7d} {Ax:9d} {Ax/x:9.4f}")
        # proportion of members by g (candidates with the same g = b - K)
        byg = {}
        for a in range(0, pxmax + 1):
            K = candidate_p(a, p)
            if K is None:
                continue
            g = a + 1 - K
            tot, m = byg.get(g, (0, 0))
            byg[g] = (tot + 1, m + (1 if allres[a][0] else 0))
        out("    g   candidates   members   proportion   (last g may be incomplete)")
        for g in sorted(byg):
            tot, m = byg[g]
            out(f"  {g:3d} {tot:11d} {m:9d}   {m/tot:9.4f}")


def first_step_p(a, p):
    """Returns (K, g, u, w0) for an exponent with a candidate, else None."""
    K = candidate_p(a, p)
    if K is None:
        return None
    g = a + 1 - K
    u = (p - 1) * K + p
    d = p ** g // u
    return K, g, u, p ** g - d * u


def immediate_predicted(p, amax):
    """Theorem (immediate failures): exponents from the triples (g, e, j)."""
    res = set()
    g = 1
    while True:
        if (p ** g - p) // (p - 1) // p > amax + 10:
            break
        for e in range(2, p):
            for j in range(1, p):
                if (p ** g + j) % e:
                    continue
                u = (p ** g + j) // e
                if u < p or (u - 1) % (p - 1) or not (u <= p ** g <= p * (u - 1)):
                    continue
                K = (u - p) // (p - 1)
                a = K + g - 1
                if a <= amax:
                    res.add(a)
        g += 1
    return res


def exp_immediate(primes, amax):
    out(f"\n== E26. Immediate failures (Theorem 9.6), a <= {amax} ==")
    for p in [2] + list(primes):
        t0 = time.time()
        if p == 2:
            # p = 2 in the indexing of Section 9: candidate K' = K - 2, w0 = 2^h - K <= K' = K - 2 always
            obs = set()
            for a in range(0, amax + 1):
                r = first_step_p(a, 2)
                if r is not None and r[3] > r[0]:
                    obs.add(a)
            check(f"p=2: no immediate failures, a <= {amax}", not obs, f"{len(obs)} found")
            continue
        obs = set()
        for a in range(0, amax + 1):
            r = first_step_p(a, p)
            if r is not None and r[3] > (p - 1) * r[0]:
                obs.add(a)
        pred = immediate_predicted(p, amax)
        out(f"  p={p}: {len(obs)} immediate failures, {time.time()-t0:.1f}s: {sorted(obs)[:30]}")
        check(f"p={p}: immediate failures = exponents of the triples (g, e, j), a <= {amax}", obs == pred,
              f"{len(obs)} observed, {len(pred)} predicted")
        if p == 3:
            fam3 = set()
            for g in range(2, 40, 2):
                K = (3 ** g - 5) // 4
                if K + g - 1 <= amax:
                    fam3.add(K + g - 1)
            check(f"p=3: immediate failures = Theorem 9.5(3), a <= {amax}", obs == fam3)
        # per g count bound (p-1)(p-2)
        byg = {}
        for a in obs:
            g = first_step_p(a, p)[1]
            byg[g] = byg.get(g, 0) + 1
        check(f"p={p}: at most (p-1)(p-2) = {(p-1)*(p-2)} immediate failures per g", all(c <= (p - 1) * (p - 2) for c in byg.values()),
              ", ".join(f"g={g}: {c}" for g, c in sorted(byg.items())))


def bottomup_p_next(S, K, p, use_np):
    """Theorem 9.7: S^{(p)}_{K+1} from S^{(p)}_K (boolean array of length (p-1)K+1)."""
    uK = (p - 1) * K + p
    L = (p - 1) * (K + 1) + 1
    if use_np:
        new = np.zeros(L, dtype=bool)
        idx = np.nonzero(S)[0]
        if K % p:
            inv = pow(uK % p, -1, p)
            d = (-idx * inv) % p
            new[(idx + d * uK) // p] = True
        else:
            B = idx[idx % p == 0] // p
            q = uK // p
            for d in range(p):
                new[B + d * q] = True
        return new
    new = [False] * L
    for w in range(len(S)):
        if not S[w]:
            continue
        for d in range(p):
            if (w + d * uK) % p == 0:
                new[(w + d * uK) // p] = True
    return new


def exp_primes_bottomup(primes, kmax, use_np):
    out(f"\n== E27. Bottom-up recursion and symmetry for odd p (Theorem 9.7), K <= {kmax} ==")
    import bisect
    for p in primes:
        km = kmax if use_np else min(kmax, 3000)
        t0 = time.time()
        S = np.ones(1, dtype=bool) if use_np else [True]
        sym_ok = pair_ok = mult_ok = True
        members = []
        byg = {}
        Nvals = []
        for K in range(0, km + 1):
            nK = int(S.sum()) if use_np else sum(S)
            Nvals.append(nK)
            if use_np:
                sym_ok &= bool(np.array_equal(S, S[::-1]))
            else:
                sym_ok &= S == S[::-1]
            # initial state of the candidate K
            g = g_of(K, p)
            a = K + g - 1
            u = (p - 1) * K + p
            dd = p ** g // u
            w0 = p ** g - dd * u
            mem = w0 <= (p - 1) * K and bool(S[w0])
            if mem:
                members.append(a)
            tot, m, dens = byg.get(g, (0, 0, 0.0))
            byg[g] = (tot + 1, m + (1 if mem else 0), dens + nK / ((p - 1) * K + 1))
            Snext = bottomup_p_next(S, K, p, use_np)
            nn = int(Snext.sum()) if use_np else sum(Snext)
            if K % p:
                pair_ok &= nn == nK
            else:
                cnt = int(S[0::p].sum()) if use_np else sum(S[0::p])
                mult_ok &= nn == p * cnt
            S = Snext
        out(f"\n  --- p = {p}: K <= {km} in {time.time()-t0:.1f}s ---")
        check(f"p={p}: symmetry w <-> (p-1)K - w, K <= {km}", sym_ok)
        check(f"p={p}: N_p(K+1) = N_p(K) for p not dividing K", pair_ok)
        check(f"p={p}: N_p(K+1) = p #{{w in S_K : p | w}} for p | K", mult_ok)
        # agreement with the recursion of Theorem 9.4
        amax_chk = min(1500, members[-1] if members else 0)
        rec = [a for a in range(0, amax_chk + 1) if membership_p(a, p)[0]]
        bu = [a for a in members if a <= amax_chk]
        check(f"p={p}: members from S_K = members from the recursion, a <= {amax_chk}", rec == bu)
        xmax_p = km + g_of(km, p) - 1
        out(f"  A_p(x) up to x = {xmax_p}:")
        out("        x     A_p(x)   A_p(x)/x")
        step = max(1000, (xmax_p // 15) // 1000 * 1000)
        ratios = []
        for x in range(step, xmax_p + 1, step):
            Ax = bisect.bisect_right(members, x)
            out(f"  {x:7d} {Ax:9d} {Ax/x:9.4f}")
        for x in range(1000, xmax_p + 1, 1000):
            ratios.append((bisect.bisect_right(members, x) / x, x))
        if ratios:
            out(f"  A_p(x)/x over x = 1000, 2000, ..., {ratios[-1][1]}: min {min(ratios)[0]:.4f} at x = {min(ratios)[1]}, "
                f"max {max(ratios)[0]:.4f} at x = {max(ratios)[1]}")
        out("    g   candidates   members   proportion   mean N_p(K)/((p-1)K+1)")
        for g in sorted(byg):
            tot, m, dens = byg[g]
            complete = (g_of(km, p) > g)
            out(f"  {g:3d} {tot:11d} {m:9d}   {m/tot:9.4f}   {dens/tot:9.4f}" + ("" if complete else "   (incomplete)"))
        # dyadic-like ranges of K: N_p(K)/((p-1)K+1)
        out("    range of K           min density   max density   mean density")
        lo = 1
        while lo <= km:
            hi = min(lo * p - 1, km)
            vals = [Nvals[K] / ((p - 1) * K + 1) for K in range(lo, hi + 1)]
            out(f"  [{lo:7d}, {hi:7d}]   {min(vals):11.4f}   {max(vals):11.4f}   {sum(vals)/len(vals):11.4f}")
            lo *= p


def exp_nicolas_families(confirm_max):
    """Proposition 7.2: number of exponents <= x in the three families of Nicolas."""
    out("\n== E28. Proposition 7.2: the three families of Nicolas ==")
    xs = [10**3, 10**4, 10**5, 10**6, 10**9, 10**12]
    xtop = max(max(xs), confirm_max)
    # first family: 2^r + r - 2, r >= 1 (no candidate K, not in A)
    fam1 = []
    r = 1
    while (1 << r) + r - 2 <= xtop:
        fam1.append((1 << r) + r - 2)
        r += 1
    # second family: a + (2^a - 11)/3, a >= 3 odd (in A)
    fam2 = []
    a = 3
    while a + ((1 << a) - 11) // 3 <= xtop:
        assert ((1 << a) - 11) % 3 == 0
        fam2.append(a + ((1 << a) - 11) // 3)
        a += 2
    # third family: a + (2^a - 10)/3, a >= 4 even (not in A)
    fam3 = []
    a = 4
    while a + ((1 << a) - 10) // 3 <= xtop:
        assert ((1 << a) - 10) % 3 == 0
        fam3.append(a + ((1 << a) - 10) // 3)
        a += 2
    out("            x   log2(x)   A_N(x)   (1/2)log2(x)   first   third   B_N(x)   (3/2)log2(x)")
    for x in xs:
        n1 = sum(1 for e in fam1 if e <= x)
        n2 = sum(1 for e in fam2 if e <= x)
        n3 = sum(1 for e in fam3 if e <= x)
        lg = math.log2(x)
        out(f"{x:13d} {lg:9.4f} {n2:8d} {lg/2:14.4f} {n1:7d} {n3:7d} {n1+n3:8d} {1.5*lg:14.4f}")
    for x in [10**3, 10**4, 10**5]:
        out(f"x = {x}: members {[e for e in fam2 if e <= x]}")
        out(f"x = {x}: non-members, first family {[e for e in fam1 if e <= x]}")
        out(f"x = {x}: non-members, third family {[e for e in fam3 if e <= x]}")
    inc = all(f[i] < f[i + 1] for f in (fam1, fam2, fam3) for i in range(len(f) - 1))
    ok_struct = (inc and not (set(fam1) & set(fam3))
                 and all(candidate_K(e) is None for e in fam1)
                 and all(candidate_K(e) is not None for e in fam3))
    check("Nicolas families: strictly increasing; first family has no candidate K, "
          "third family has one; first and third disjoint", ok_struct)
    t0 = time.time()
    ok_mem = all(membership(e)["member"] for e in fam2 if e <= confirm_max)
    ok_non = all(not membership(e)["member"] for e in fam1 + fam3 if e <= confirm_max)
    check(f"Nicolas families: Algorithm 1 confirms members and non-members for exponents <= {confirm_max}",
          ok_mem and ok_non, f"{time.time()-t0:.1f}s")


def exp_zero_step_p(primes, amax, kcheck):
    """Exponents a with candidate K and w_0 = 0, against K = (p^g - p)/(p - 1)."""
    out(f"\n== E29. Exponents accepted without any step (w_0 = 0), a <= {amax} ==")
    for p in [2] + [q for q in primes if q != 2]:
        t0 = time.time()
        observed = []
        ok_u = True
        for a in range(0, amax + 1):
            fs = first_step_p(a, p)
            if fs is None:
                continue
            K, g, u, w0 = fs
            if w0 == 0:
                observed.append(a)
                ok_u &= (u == p ** g) and (K * (p - 1) == p ** g - p)
            else:
                ok_u &= (u != p ** g)
        predicted = []
        g = 1
        while (p ** g - p) // (p - 1) + g - 1 <= amax:
            predicted.append((p ** g - p) // (p - 1) + g - 1)
            g += 1
        out(f"  p={p}: {len(observed)} exponents with w_0 = 0, {time.time()-t0:.1f}s: {observed}")
        check(f"p={p}: w_0 = 0 if and only if u = p^g, a <= {amax}", ok_u)
        check(f"p={p}: exponents with w_0 = 0 = exponents K + g - 1 with K = (p^g - p)/(p - 1), a <= {amax}",
              observed == predicted, f"{len(observed)} observed, {len(predicted)} predicted")
        ok_m = all(membership_p(a, p) == (True, "success", 0) for a in observed)
        check(f"p={p}: these exponents are accepted by the recursion with 0 steps", ok_m)
        ok_c = True
        nck = 0
        g = 1
        while (p ** g - p) // (p - 1) <= kcheck:
            K = (p ** g - p) // (p - 1)
            ok_c &= cp_formula(p ** K, p) == p ** (K + g - 1)
            nck += 1
            g += 1
        check(f"p={p}: c_p(p^K) = p^(K+g-1) for K = (p^g - p)/(p - 1) <= {kcheck}", ok_c, f"{nck} values of g")


def family_exponents(H):
    """Family exponents with h <= H: (members of Theorems 5.1; non-members of Theorems 3.3, 6.1;
    members with Theorem 8.7(1),(2) added; non-members with Theorem 8.7(3) added)."""
    mem71, non71 = set(), set((1 << r) + r - 2 for r in range(1, H + 1))
    sym_mem, sym_non = set(), set()
    for h in range(1, H + 1):
        mem71.add(beta(1 << h) - 3)
        for k in range(0, h):
            s = 1 << k
            if h >= k + 2 and (h - k) % (1 << (k + 1)) == 0:
                K = ((1 << (h + s)) + s) // ((1 << s) + 1)
                mem71.add(K + h - 3)
        fams = [(1 << i) for i in range(1, h) if (h - i) % (2 * ((1 << i) - 1)) == 0]
        if h % 4 == 3:
            fams.append(3)
        for s in fams:
            K = ((1 << (h + s - 1)) + s) // ((1 << (s - 1)) + 1)
            non71.add(K + h - 3)
        if h >= 3:
            sym_mem.add((1 << (h - 1)) + 1 + h - 3)
        i = 1
        while True:
            sg = (1 << (i - 1)) + 1
            if h < sg + 2:
                break
            if (h - i) % (sg + 1) == 0:
                w = ((1 << h) - 2 * sg + 2) // ((1 << (sg + 1)) - 1)
                sym_mem.add((1 << (h - 1)) + 1 + w // 2 + h - 3)
            i += 1
        i = 2
        while True:
            sg = (1 << (i - 1)) + 1
            if h < sg + 1:
                break
            if (h - i) % sg == 0:
                w = ((1 << h) - 2 * sg + 2) // ((1 << sg) - 1)
                sym_non.add((1 << (h - 1)) + 1 + w // 2 + h - 3)
            i += 1
    return mem71, non71, mem71 | sym_mem, non71 | sym_non


def exp_explicit_bounds(amax_alg):
    """Explicit forms of Theorems 7.1 and 8.8, valid for x >= 16, H = floor(log2 x) - 1."""
    out("\n== E30. Explicit lower bounds of Theorems 7.1 and 8.8 ==")
    C1 = sum(1.0 / ((1 << k) + 2) for k in range(0, 200))
    C2 = sum(1.0 / ((1 << k) + 1) for k in range(1, 200))
    E = sum(1.0 / ((1 << i) - 1) for i in range(1, 200))
    out("  bA1 = 2H - log2(H) - 3,  bB1 = (5/4 + E/2)H - log2(H) - 5   (Theorem 7.1)")
    out("  bA2 = (3 + C1)H - 3 log2(H) - 10,  bB2 = (5/4 + E/2 + C2)H - 3 log2(H) - 9   (Theorem 8.8)")
    out("  mem1/non1: family exponents of Theorem 7.1; mem2/non2: with the families of Theorem 8.7 added")
    out("            x    H   mem1      bA1   non1      bB1   mem2      bA2   non2      bB2")
    ok = True
    ok_alg = True
    for x in [16, 64, 256, 1000, 4096, 10**4, 65536, 10**5, 10**6, 10**9, 10**12]:
        H = int(math.floor(math.log2(x))) - 1
        m1, n1, m2, n2 = family_exponents(H)
        L = math.log2(H)
        bA1 = 2 * H - L - 3
        bB1 = (1.25 + E / 2) * H - L - 5
        bA2 = (3 + C1) * H - 3 * L - 10
        bB2 = (1.25 + E / 2 + C2) * H - 3 * L - 9
        ok &= len(m1) >= bA1 and len(n1) >= bB1 and len(m2) >= bA2 and len(n2) >= bB2
        ok &= max(m2) <= x and max(n2) <= x and not (m2 & n2)
        if x <= amax_alg:
            ok_alg &= all(membership(a)["member"] for a in m2)
            ok_alg &= all(not membership(a)["member"] for a in n2)
        out(f"{x:13d} {H:4d} {len(m1):6d} {bA1:8.2f} {len(n1):6d} {bB1:8.2f} {len(m2):6d} {bA2:8.2f} {len(n2):6d} {bB2:8.2f}")
    check("number of family exponents >= explicit bound (four bounds), exponents <= x, members and non-members disjoint", ok)
    check(f"Algorithm 1 confirms the family exponents used, x <= {amax_alg}", ok_alg)


def is_power(x, p):
    if x < 1:
        return False
    while x % p == 0:
        x //= p
    return x == 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lemma-n", type=int, default=1 << 20, help="E1 range")
    ap.add_argument("--brute-log", type=int, default=24, help="E2: brute force up to n = 2^brute_log")
    ap.add_argument("--greedy-max", type=int, default=4000, help="E4: big-integer greedy up to a")
    ap.add_argument("--xmax", type=int, default=10000, help="E5: A(x) table up to x")
    ap.add_argument("--hmax-formula", type=int, default=300, help="E6/E7: closed-form checks up to h")
    ap.add_argument("--hmax-alg", type=int, default=18, help="E6/E7: Algorithm 1 checks up to h")
    ap.add_argument("--jmax", type=int, default=1 << 16, help="E9-E16: successful states up to level J")
    ap.add_argument("--no-numpy", action="store_true", help="E9-E16: force pure Python (slow)")
    ap.add_argument("--jmax2", type=int, default=1 << 18, help="E20-E23: bottom-up recursion up to level J")
    ap.add_argument("--primes", type=str, default="3,5,7", help="E25: odd primes p")
    ap.add_argument("--pxmax", type=int, default=6000, help="E25: A_p(x) up to x")
    ap.add_argument("--imax", type=int, default=100000, help="E26: immediate failures up to a")
    ap.add_argument("--kmax", type=int, default=20000, help="E27: bottom-up recursion for odd p up to K")
    ap.add_argument("--nicolas-max", type=int, default=10**6,
                    help="E28: Algorithm 1 confirmation of the families of Nicolas up to this exponent")
    args = ap.parse_args()

    out("Experiments for: Powers of Two in the Image of the Summatory Function of 2^{v_2(k)}")
    out(f"Python {sys.version.split()[0]}; parameters: {vars(args)}")
    T0 = time.time()
    exp_lemma(args.lemma_n)
    exp_bruteforce(args.brute_log)
    exp_theorem_leading(5000)
    exp_algorithm_vs_greedy(args.greedy_max)
    members = exp_counting_table(args.xmax)
    exp_member_families(args.hmax_formula, args.hmax_alg, args.greedy_max)
    exp_nonmember_families(args.hmax_formula, args.hmax_alg, args.greedy_max)
    exp_counting_bounds(members, args.xmax)
    use_np = HAVE_NP and not args.no_numpy
    jmax = args.jmax if use_np else min(args.jmax, 8192)
    if jmax != args.jmax:
        out(f"numpy not available: jmax reduced to {jmax}")
    res = exp_states(jmax, use_np)
    exp_forest(jmax, res)
    jmax2 = args.jmax2 if use_np else min(args.jmax2, 16384)
    exp_bottomup(max(jmax2, jmax), res, use_np)
    primes = [int(q) for q in args.primes.split(",")]
    exp_primes(primes, args.pxmax)
    exp_immediate(primes, args.imax)
    exp_primes_bottomup(primes, args.kmax, use_np)
    exp_nicolas_families(args.nicolas_max)
    exp_zero_step_p(primes, args.imax, 3000)
    exp_explicit_bounds(100000)
    out(f"\nTotal time: {time.time()-T0:.1f}s")
    out("SUMMARY: " + ("all checks PASS" if not FAILURES else f"{len(FAILURES)} FAIL: {FAILURES}"))
    path = Path(__file__).resolve().parent / "results_powers_of_two_c.txt"
    path.write_text("\n".join(OUT_LINES) + "\n", encoding="utf-8")
    print(f"results written to {path}")


if __name__ == "__main__":
    main()
