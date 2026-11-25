# Formalization notes

This document states what the Lean development proves and what it does not touch.

## Main result

Theorem `thm:equiv` of the paper, `SequenceNicolas.Core.equiv_repr`: for `a ≥ 0`, `2^a` is a value of `c(n) = ∑_{k=1}^{n} 2^{v_2(k)}` if and only if `2^(a+3) = ∑_{j ∈ T} j 2^j` for a finite set `T` of positive integers. The question of Nicolas on the behaviour of `A(x)` is not answered by the paper and is not claimed in Lean.

## Toolchain

The development builds with Lean `v4.35.0-rc2` and the Mathlib tag `v4.35.0-rc2`, as the Palomar comparator requires.

## Definitions

`c n = ∑ k ∈ Finset.Icc 1 n, 2 ^ padicValNat 2 k`, where `padicValNat 2 k` is the exponent `v_2(k)` of `2` in `k`. The set `E` of the paper is expressed directly: `n ∈ E` means `n = ∑ j ∈ T, j * 2 ^ j` for a finite set `T` of positive integers. The set `B(n)` of the binary exponents of `n` is replaced by an arbitrary finite set `S` of exponents with `n = ∑ i ∈ S, 2 ^ i`; `exists_pow_sum` shows that such a set exists for every `n`.

## Proved in Lean (`SequenceNicolas/Core.lean`)

* `c_double`, `c_double_succ`: `c(2n) = 2c(n) + n` and `c(2n+1) = 2c(n) + n + 1`.
* `two_mul_c_pow`: Lemma `lem:cformula`, `2 c(2^r) = 2^r (r+2)`.
* `c_add_pow`: `c(2^a + t) = c(2^a) + c(t)` for `t < 2^a`.
* `exists_pow_sum`: every `n` is a sum `∑_{i ∈ S} 2^i` over a finite set `S`.
* `two_mul_c_sum`: formula `eq:cformula`, `2 c(n) = 2n + ∑_{i ∈ S} i 2^i` for `n = ∑_{i ∈ S} 2^i`.
* `eight_mul_c`: `8 c(n) = ∑_{i ∈ S} (i+2) 2^(i+2)`, the identity used in the proof of Theorem `thm:equiv`.
* `repr_no_one`: if `T` consists of positive integers and `∑_{j ∈ T} j 2^j = 2^(a+3)`, then `1 ∉ T` (Theorem `thm:equiv`).
* `equiv_repr`: Theorem `thm:equiv`, `(∃ n, c n = 2^a) ↔ ∃ T, (∀ j ∈ T, 1 ≤ j) ∧ ∑_{j ∈ T} j 2^j = 2^(a+3)`.
* `sum_j_two_pow`: Lemma `lem:sum`, `∑_{j=1}^{J} j 2^j + 2^(J+1) = J 2^(J+1) + 2`.
* `leading_term`: Theorem `thm:leading` (1). If `T` consists of positive integers with maximum `K` and `∑_{j ∈ T} j 2^j = 2^b`, `b ≥ 3`, then `K ≥ 2` and there is `g` with `K ≤ 2^g < 2K` and `b = K + g`, so `g = ⌈log₂ K⌉` and `b = β(K)`.
* `members_one`: Theorem `thm:members` (1), `8 c(2^(2^r - 2)) = 2^(2^r + r)` for `r ≥ 1`.
* `members_two`: Theorem `thm:members` (2), identity `eq:member`: from `K (2^s + 1) = 2^(h+s) + s`, `s ≥ 1` and `s + 2 ≤ K`, `8 c(2^(K-2) + 2^(K-s-2)) = 2^(K+h)`.
* `members_two_bounds`: Theorem `thm:members` (2), `2^(h-1) < K < 2^h`, written `2^h < 2K` and `K < 2^h`, from the same equation and `s < 2^h`.

`comparator.json` lists the public versions (namespace `SequenceNicolas.Public`) of `c_double`, `c_double_succ`, `two_mul_c_pow`, `c_add_pow`, `exists_pow_sum`, `two_mul_c_sum`, `eight_mul_c`, `repr_no_one`, `equiv_repr`, `sum_j_two_pow`, `leading_term`, `members_one`, `members_two`, `members_two_bounds`, `hfun_spec`, `hfun_of_bounds`, `hfun_succ`, `beta_strictMono`, `beta_two_pow` and `beta_two_pow_succ`; `Challenge.lean` imports only Mathlib and contains only the definitions and lemmas that these statements need, and `Solution.lean` proves the same statements from the project module. The other public theorems of `Solution.lean` are proved in the project modules and are not in the comparator selection.

## Map from the statements of the paper to Lean

| Paper label | Status | Lean |
|---|---|---|
| `lem:cformula` | formalized | `two_mul_c_pow`, `c_add_pow`, `exists_pow_sum`, `two_mul_c_sum` |
| `thm:equiv` | formalized | `eight_mul_c`, `repr_no_one`, `equiv_repr` |
| `lem:sum` | formalized | `sum_j_two_pow` |
| `lem:greedy` | not formalized | |
| `thm:leading` | part (1) formalized | `leading_term`; parts (2) and (3) not formalized |
| `thm:step`, `cor:algo`, `lem:least` | not formalized | recursion on states; checked by the experiments |
| `thm:members` | formalized | `members_one`, `members_two`, `members_two_bounds` |
| `lem:order`, `thm:nonmembers`, `thm:firststep`, `prop:nicolasfamilies` | not formalized | checked by the experiments |
| `thm:counting`, `prop:nicolascount`, `thm:counting2` | not formalized | asymptotic and explicit counting bounds |
| `prop:Ncount`, `prop:symmetry`, `prop:Npairs`, `thm:forest`, `prop:roots`, `thm:bottomup`, `thm:symfamilies` | not formalized | successful states |
| `prop:Fp`, `lem:cp`, `thm:primes`, `thm:primestep`, `thm:primefamilies`, `thm:immediate`, `thm:primebottomup`, `prop:primezero` | not formalized | arbitrary prime |
| Section `sec:experiments` | not formalized | `experiments/powers_of_two_c.py`, output in `experiments/results_powers_of_two_c.txt` |

No result of the literature is used as a hypothesis: the formalized statements are proved from Mathlib.
