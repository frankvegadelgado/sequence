# Formalization notes

This document states what the Lean development proves and what it does not touch.

## Main result

Theorem `thm:equiv` of the paper, `SequenceNicolas.Core.equiv_repr`: for `a ≥ 0`, `2^a` is a value of `c(n) = ∑_{k=1}^{n} 2^{v_2(k)}` if and only if `2^(a+3) = ∑_{j ∈ T} j 2^j` for a finite set `T` of positive integers. The question of Nicolas on the behaviour of `A(x)` is not answered by the paper and is not claimed in Lean.

## Toolchain

The development builds with Lean `v4.35.0-rc2` and the Mathlib tag `v4.35.0-rc2`, as the Palomar comparator requires.

## Definitions

`c n = ∑ k ∈ Finset.Icc 1 n, 2 ^ padicValNat 2 k`, where `padicValNat 2 k` is the exponent `v_2(k)` of `2` in `k`. The set `E` of the paper is expressed directly: `n ∈ E` means `n = ∑ j ∈ T, j * 2 ^ j` for a finite set `T` of positive integers. The set `B(n)` of the binary exponents of `n` is replaced by an arbitrary finite set `S` of exponents with `n = ∑ i ∈ S, 2 ^ i`; `exists_pow_sum` shows that such a set exists for every `n`.

## Proved in Lean

The modules are `SequenceNicolas.Core`, `Recursion`, `Families`, `States`, `Forest`, `Roots`, `SymFamilies`, `NicolasCount`, `CountBase`, `Counting`, `CountingA`, `CountingB`, `CountingC`, `CountingD`, `CountingReal`, `PrimesBase`, `PrimesRep`, `PrimesStep`, `PrimesFamilies`, `PrimesImmediate`, `PrimesBottomUp`, `PrimesFp`, `PrimesCount` and `PrimesCountReal`. The table maps each statement of the paper to its Lean theorems.

| Paper | Lean modules (`SequenceNicolas.*`) | Lean theorems |
|---|---|---|
| Introduction recurrences | Core | `c_double`, `c_double_succ` |
| `lem:cformula` | Core | `two_mul_c_pow`, `c_add_pow`, `exists_pow_sum`, `two_mul_c_sum` |
| `thm:equiv` | Core | `eight_mul_c`, `repr_no_one`, `equiv_repr` |
| `lem:sum` | Core, Recursion | `sum_j_two_pow`, `InE_lt` |
| `lem:greedy` | Recursion | `repr_unique`, `greedy_iff` |
| `thm:leading` (1) | Core, Recursion | `leading_term`, `leading_beta` |
| `thm:leading` (2), (3) and last statement | Recursion | `beta_strictMono`, `beta_range`, `leading_state`, `inE_two_pow_iff`, `amem_gap`, `exists_candidate`, `amem_iff_state` |
| `thm:step` | Recursion | `exists_S`, `term_le_iff`, `step_main` |
| `alg:membership`, `cor:algo` | Recursion | `run_sound`, `run_complete`, `int_bound` |
| `lem:least` | Recursion | `least_char`, `fails_iff`, `least_two`, `least_three` |
| `thm:members` | Core, Counting | `members_one`, `members_two`, `members_two_bounds`, `M1_spec` |
| `lem:order` | Families | `order_one`, `order_two`, `order_bounds`, `order_iff` |
| `thm:nonmembers` | Families | `nonmembers_core`, `nonmem_family_one`, `nonmem_family_two` |
| `thm:firststep` | Families | `firststep_one`, `onestep_iff`, `firststep_two`, `firststep_three` |
| `prop:nicolasfamilies` | Families | `nicolas_one`, `nicolas_two_fwd`, `nicolas_two_bwd`, `nicolas_three_fwd`, `nicolas_three_bwd` |
| `prop:nicolascount` | NicolasCount | `A_lower`, `A_upper`, `A_real`, `P_lower`, `P_upper`, `Q_lower`, `Q_upper`, `PQ_disjoint`, `B_real` |
| `thm:counting` | CountBase, Counting, CountingA, CountingB, CountingReal | `counting_A`, `counting_B`, `counting_real_A`, `counting_real_B`, `counting_real_asymp_A`, `counting_real_asymp_B` |
| `prop:Ncount` (1) | Forest | `Ncount` |
| `prop:symmetry` | States | `succ_symm` |
| `prop:Npairs` | Forest, Roots | `N_odd_eq`, `four_dvd` |
| `thm:forest` | Forest, States, Roots | `F_count`, `F_sum`, `phi_iff`, `children_card`, `succ_iff_phi`, `count_children`, `N_identity`, `J_identity`, `initial_fwd` |
| `prop:roots` | Roots | `phi_repr`, `root_of_repr`, `roots_half` |
| `thm:bottomup` | States | `bottomup_iff` |
| `thm:symfamilies` | SymFamilies | `symfam_one`, `symfam_two`, `symfam_three` |
| `thm:counting2` | CountingC, CountingD, CountingReal | `counting2_A`, `counting2_B`, `counting2_real_A`, `counting2_real_B`, `counting2_real_asymp_A`, `counting2_real_asymp_B` |
| `lem:cp` | PrimesBase | `cp_mul`, `cp_pow`, `cp_pow_pred`, `cp_digits` |
| `prop:Fp` | PrimesFp | `prop_Fp`, `prop_Fp_unique` |
| `thm:primes` | PrimesRep | `rep_unique`, `Ap_iff`, `bp_gap_of`, `unique_candidate`, `not_Ap_gap`, `Ap_cand` |
| `thm:primestep` | PrimesStep | `primestep_one`, `primestep_two` |
| `thm:primefamilies` | PrimesFamilies, PrimesCount, PrimesCountReal | `primefam_one`, `primefam_two`, `primefam_three`, `primecount_A`, `primecount_B`, `primecount_real_A`, `primecount_real_B` |
| `prop:primezero` | PrimesFamilies | `primezero_iff`, `primezero_mem`, `primezero_family` |
| `thm:immediate` | PrimesImmediate | `imm_range`, `imm_two`, `imm_triple`, `imm_param`, `imm_three`, `imm_count` |
| `thm:primebottomup` | PrimesBottomUp | `succ_succ_iff`, `succ_pair_inj`, `N_succ_not_dvd`, `N_succ_dvd`, `succ_dvd_iff`, `succ_dvd_inj`, `succ_symm`, `Ap_iff_Sset` |

`comparator.json` lists the public versions (namespace `SequenceNicolas.Public`) of `c_double`, `c_double_succ`, `two_mul_c_pow`, `c_add_pow`, `exists_pow_sum`, `two_mul_c_sum`, `eight_mul_c`, `repr_no_one`, `equiv_repr`, `sum_j_two_pow`, `leading_term`, `members_one`, `members_two`, `members_two_bounds`, `hfun_spec`, `hfun_of_bounds`, `hfun_succ`, `beta_strictMono`, `beta_two_pow` and `beta_two_pow_succ`; `Challenge.lean` imports only Mathlib and contains the definitions and lemmas that these statements need, and `Solution.lean` proves the same statements from the project module. 

## Not formalized in Lean

- Proposition `prop:Ncount` (2).
- The computations and tables of Section `sec:experiments`.

No result of the literature is used as a hypothesis: the formalized statements are proved from Mathlib.
