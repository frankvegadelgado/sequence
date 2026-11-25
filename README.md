# SequenceNicolas: powers of a prime in the image of summatory valuation functions

Lean 4 formalization for *Powers of a Prime in the Image of Summatory Valuation Functions* (`doc/paper.tex`). `formalization.yaml` is the machine-readable inventory; this file explains it.

## Main result

Theorem `thm:equiv` of the paper, Lean theorem `equiv_repr`: for `c(n) = ∑_{k=1}^{n} 2^{v_2(k)}` and `a ≥ 0`, there is `n` with `c(n) = 2^a` if and only if `2^(a+3) = ∑_{j ∈ T} j 2^j` for a finite set `T` of positive integers (that is, `2^(a+3)` is a sum of distinct terms of the superincreasing sequence `(j 2^j)_{j ≥ 1}`). The paper does not determine the asymptotic behaviour of `A(x)` asked for by Nicolas. The Lean development proves the statements of the paper listed below, including the recursion on states, the explicit families, the counting bounds, the successful states and the analogue for an arbitrary prime.

## Repository layout

| Path | Content |
| --- | --- |
| `doc/paper.tex` | The manuscript. |
| `doc/biblio.bib` | The bibliography (BibTeX style `plainurl`). |
| `doc/formalization.md` | What Lean proves and what it does not. |
| `formalization.yaml` | Module inventory with status. |
| `SequenceNicolas/*.lean` | The Lean modules, listed in the table below. |
| `Challenge.lean`, `Solution.lean` | Standalone challenge (imports only Mathlib) and its solution, compared by `lake comparator`. |
| `comparator.json` | The compared theorems, in the namespace `SequenceNicolas.Public`. |
| `scripts/` | `check-lean-sources.py`, `verify-comparator.sh`. |
| `experiments/` | `powers_of_two_c.py` and its output `results_powers_of_two_c.txt`. |

## Lean theorems

`c n` is `∑ k ∈ Icc 1 n, 2 ^ padicValNat 2 k`, and `cp p n` is `∑_{k=1}^{n} p^{v_p(k)}`.

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

## Not formalized in Lean

- Proposition `prop:Ncount` (2).
- The computations and tables of Section `sec:experiments`.

## Toolchain

Lean `v4.35.0-rc2` with Mathlib tag `v4.35.0-rc2` (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`). The Palomar comparator requires this toolchain or later.

## Building and verifying

```bash
lake build
python3 scripts/check-lean-sources.py
bash scripts/verify-comparator.sh
```

## License

Apache-2.0 (`LICENSE`).

## Compiling the paper

`doc/paper.tex` uses the `amsart` class and `doc/biblio.bib` with the BibTeX style `plainurl` (package `urlbst`; `hyperref` is loaded because `plainurl` uses `\href`). From the `doc` folder:

```
pdflatex paper
bibtex paper
pdflatex paper
pdflatex paper
```

The resulting `paper.pdf` and the auxiliary files are ignored by git.

## Experiments

The script of the computational section of the paper is `experiments/powers_of_two_c.py`. It needs no package of this repository (Python 3.12; NumPy is optional). The run reported in the paper is

```
python experiments/powers_of_two_c.py --xmax 20000 --jmax2 262144 --pxmax 6000 --primes 3,5,7,11 --kmax 20000
```

and its output is `experiments/results_powers_of_two_c.txt`.

The complete map from the labelled statements of the paper to Lean theorems and computations is in `doc/formalization.md`.
