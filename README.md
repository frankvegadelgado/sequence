# SequenceNicolas: powers of a prime in the image of summatory valuation functions

Lean 4 formalization for *Powers of a Prime in the Image of Summatory Valuation Functions* (`doc/paper.tex`). `formalization.yaml` is the machine-readable inventory; this file explains it.

## Main result

Theorem `thm:equiv` of the paper, Lean theorem `equiv_repr`: for `c(n) = ∑_{k=1}^{n} 2^{v_2(k)}` and `a ≥ 0`, there is `n` with `c(n) = 2^a` if and only if `2^(a+3) = ∑_{j ∈ T} j 2^j` for a finite set `T` of positive integers (that is, `2^(a+3)` is a sum of distinct terms of the superincreasing sequence `(j 2^j)_{j ≥ 1}`). The paper does not determine the asymptotic behaviour of `A(x)` asked for by Nicolas; the Lean development covers the elementary statements of the paper and states which results it does not touch.

## Repository layout

| Path | Content |
| --- | --- |
| `doc/paper.tex` | The manuscript. |
| `doc/biblio.bib` | The bibliography (BibTeX style `plainurl`). |
| `doc/formalization.md` | What Lean proves and what it does not. |
| `formalization.yaml` | Module inventory with status. |
| `SequenceNicolas/Core.lean` | The formalized statements of the paper. |
| `Challenge.lean`, `Solution.lean` | Standalone challenge (imports only Mathlib) and its solution, compared by `lake comparator`. |
| `comparator.json` | The compared theorems, in the namespace `SequenceNicolas.Public`. |
| `scripts/` | `check-lean-sources.py`, `verify-comparator.sh`. |
| `experiments/` | `powers_of_two_c.py` and its output `results_powers_of_two_c.txt`. |

## Lean theorems

The theorems are in `SequenceNicolas/Core.lean`; `c n` is `∑ k ∈ Icc 1 n, 2 ^ padicValNat 2 k`.

| Theorem | Paper |
| --- | --- |
| `c_double`, `c_double_succ` | Recurrences `c(2n) = 2c(n) + n` and `c(2n+1) = 2c(n) + n + 1` (Introduction, Related work) |
| `two_mul_c_pow` | Lemma `lem:cformula`: `c(2^r) = 2^(r-1) (r+2)`, written `2 c(2^r) = 2^r (r+2)` |
| `c_add_pow` | Proof of Lemma `lem:cformula`: `c(2^m + s) = c(2^m) + c(s)` for `s < 2^m` |
| `exists_pow_sum`, `two_mul_c_sum` | Formula `eq:cformula`: `2 c(n) = 2n + ∑_{i ∈ B(n)} i 2^i` for `n = ∑_{i ∈ B(n)} 2^i` (stated for every finite set of exponents) |
| `eight_mul_c` | Proof of Theorem `thm:equiv`: `8 c(n) = ∑_{j ∈ B(n)+2} j 2^j` |
| `repr_no_one`, `equiv_repr` | Theorem `thm:equiv` |
| `sum_j_two_pow` | Lemma `lem:sum`: `∑_{j=1}^{J} j 2^j = (J-1) 2^(J+1) + 2`, written without subtraction |
| `leading_term` | Theorem `thm:leading` (1): the largest element `K` of the representing set satisfies `K ≥ 2` and `b = K + ⌈log₂ K⌉`, with `⌈log₂ K⌉` characterized by `K ≤ 2^g < 2K` |
| `members_one` | Theorem `thm:members` (1): `c(2^(2^r - 2)) = 2^(2^r + r - 3)`, written `8 c(2^(2^r - 2)) = 2^(2^r + r)` |
| `members_two`, `members_two_bounds` | Theorem `thm:members` (2): `c(2^(K-2) + 2^(K-s-2)) = 2^(K+h-3)` and `2^(h-1) < K < 2^h`, from `K (2^s + 1) = 2^(h+s) + s` |

## Not formalized in Lean

- Lemma `lem:greedy` and parts (2) and (3) of Theorem `thm:leading`.
- The recursion on states: Theorem `thm:step`, Corollary `cor:algo`, Lemma `lem:least`.
- Lemma `lem:order`, the explicit non-members (Theorem `thm:nonmembers`) and Theorem `thm:firststep`, Proposition `prop:nicolasfamilies`.
- The counting bounds (Theorems `thm:counting` and `thm:counting2`, Proposition `prop:nicolascount`).
- The successful states, the forest and the bottom-up recursion (Section `sec:states`).
- The analogue for an arbitrary prime (Section `sec:primes`).
- The computations of Section `sec:experiments`.

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
