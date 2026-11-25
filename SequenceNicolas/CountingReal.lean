module

public import Mathlib
public import SequenceNicolas.CountBase
public import SequenceNicolas.Counting
public import SequenceNicolas.CountingA
public import SequenceNicolas.CountingB
public import SequenceNicolas.CountingD

@[expose] public section

/-!
# The counting bounds for a real argument

`A(x) = #{a ∈ 𝓐 : a ≤ x}` and `B(x) = #{0 ≤ a ≤ x : a ∉ 𝓐}` for real `x` are `Acount ⌊x⌋₊` and
`Bcount ⌊x⌋₊`, and `H = ⌊log₂ x⌋ - 1`.
-/

namespace SequenceNicolas.Counting

open SequenceNicolas.CountBase

/-- `H = ⌊log₂ x⌋ - 1`. -/
noncomputable def Hx (x : ℝ) : ℕ := ⌊Real.logb 2 x⌋₊ - 1

theorem Hx_facts {x : ℝ} (hx : 16 ≤ x) :
    3 ≤ Hx x ∧ 2 ^ (Hx x + 1) ≤ ⌊x⌋₊ ∧ Real.logb 2 x - 2 < (Hx x : ℝ) ∧
      (Hx x : ℝ) ≤ Real.logb 2 x - 1 := by
  have hpos : 0 < x := by linarith
  have hlb : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) (by linarith)
  have h4 : (4 : ℝ) ≤ Real.logb 2 x := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hpos]
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    linarith [(by norm_num : (2 : ℝ) ^ 4 = 16)]
  have hL4 : 4 ≤ ⌊Real.logb 2 x⌋₊ := Nat.le_floor (by exact_mod_cast h4)
  have hLle : ((⌊Real.logb 2 x⌋₊ : ℕ) : ℝ) ≤ Real.logb 2 x := Nat.floor_le hlb
  have hLlt : Real.logb 2 x < ((⌊Real.logb 2 x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  unfold Hx
  obtain ⟨L, hL⟩ : ∃ L, L = ⌊Real.logb 2 x⌋₊ := ⟨_, rfl⟩
  rw [← hL] at hL4 hLle hLlt ⊢
  have hHL : (((L - 1 : ℕ)) : ℝ) = (L : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ L)]
    norm_num
  have hpow : (2 : ℝ) ^ L ≤ x := by
    have := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hpos).1 hLle
    rwa [Real.rpow_natCast] at this
  refine ⟨by omega, ?_, by rw [hHL]; linarith, by rw [hHL]; linarith⟩
  have e : L - 1 + 1 = L := by omega
  rw [e]
  exact Nat.le_floor (by push_cast; exact hpow)

/-- Theorem `thm:counting`, `A(x) ≥ 2H - log₂ H - 3` for `x ≥ 16`. -/
theorem counting_real_A {x : ℝ} (hx : 16 ≤ x) :
    2 * (Hx x : ℝ) - Real.logb 2 (Hx x : ℝ) - 3 ≤ (Acount ⌊x⌋₊ : ℝ) := by
  obtain ⟨h1, h2, _, _⟩ := Hx_facts hx
  exact counting_A h2 h1

/-- Theorem `thm:counting`, `B(x) ≥ (5/4 + E/2) H - log₂ H - 5` for `x ≥ 16`. -/
theorem counting_real_B {x : ℝ} (hx : 16 ≤ x) :
    (5 / 4 + Econst / 2) * (Hx x : ℝ) - Real.logb 2 (Hx x : ℝ) - 5 ≤ (Bcount ⌊x⌋₊ : ℝ) := by
  obtain ⟨h1, h2, _, _⟩ := Hx_facts hx
  exact counting_B h2 h1

/-- Theorem `thm:counting2`, first bound, for `x ≥ 16`. -/
theorem counting2_real_A {x : ℝ} (hx : 16 ≤ x) :
    (3 + C1const) * (Hx x : ℝ) - 3 * Real.logb 2 (Hx x : ℝ) - 10 ≤ (Acount ⌊x⌋₊ : ℝ) := by
  obtain ⟨h1, h2, _, _⟩ := Hx_facts hx
  exact counting2_A h2 h1

/-- Theorem `thm:counting2`, second bound, for `x ≥ 16`. -/
theorem counting2_real_B {x : ℝ} (hx : 16 ≤ x) :
    (5 / 4 + Econst / 2 + C2const) * (Hx x : ℝ) - 3 * Real.logb 2 (Hx x : ℝ) - 9 ≤
      (Bcount ⌊x⌋₊ : ℝ) := by
  obtain ⟨h1, h2, _, _⟩ := Hx_facts hx
  exact counting2_B h2 h1

theorem Econst_nonneg : 0 ≤ Econst := by
  unfold Econst
  apply tsum_nonneg
  intro i
  show 0 ≤ 1 / ((2 : ℝ) ^ (i + 1) - 1)
  have : (1 : ℝ) ≤ 2 ^ (i + 1) := by exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ (i + 1))
  exact div_nonneg zero_le_one (by linarith)

theorem C1const_nonneg : 0 ≤ C1const := by
  unfold C1const
  apply tsum_nonneg
  intro k
  show 0 ≤ 1 / ((2 : ℝ) ^ k + 2)
  positivity

theorem C2const_nonneg : 0 ≤ C2const := by
  unfold C2const
  apply tsum_nonneg
  intro k
  show 0 ≤ 1 / ((2 : ℝ) ^ (k + 1) + 1)
  positivity

/-- From the bounds in `H` to the bounds in `log₂ x` and `log₂ log₂ x`. -/
theorem real_reduce {x c d e N : ℝ} (hx : 16 ≤ x) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : c * (Hx x : ℝ) - d * Real.logb 2 (Hx x : ℝ) - e ≤ N) :
    c * Real.logb 2 x - d * Real.logb 2 (Real.logb 2 x) - (2 * c + e) ≤ N := by
  obtain ⟨h1, _, h3, h4⟩ := Hx_facts hx
  have hH0 : (3 : ℝ) ≤ (Hx x : ℝ) := by exact_mod_cast h1
  have hlog : Real.logb 2 (Hx x : ℝ) ≤ Real.logb 2 (Real.logb 2 x) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  have e1 := mul_le_mul_of_nonneg_left h3.le hc
  have e2 := mul_le_mul_of_nonneg_left hlog hd
  nlinarith [e1, e2]

/-- Theorem `thm:counting`: `A(x) ≥ 2 log₂ x - log₂ log₂ x - 7` for `x ≥ 16`, so
`A(x) ≥ 2 log₂ x - O(log log x)`. -/
theorem counting_real_asymp_A {x : ℝ} (hx : 16 ≤ x) :
    2 * Real.logb 2 x - Real.logb 2 (Real.logb 2 x) - 7 ≤ (Acount ⌊x⌋₊ : ℝ) := by
  have h := real_reduce (c := 2) (d := 1) (e := 3) (N := (Acount ⌊x⌋₊ : ℝ)) hx
    (by norm_num) (by norm_num) (by have := counting_real_A hx; linarith)
  linarith

/-- Theorem `thm:counting`: `B(x) ≥ (5/4 + E/2) log₂ x - O(log log x)`. -/
theorem counting_real_asymp_B {x : ℝ} (hx : 16 ≤ x) :
    (5 / 4 + Econst / 2) * Real.logb 2 x - Real.logb 2 (Real.logb 2 x) -
        (2 * (5 / 4 + Econst / 2) + 5) ≤ (Bcount ⌊x⌋₊ : ℝ) := by
  have hE := Econst_nonneg
  have h := real_reduce (c := 5 / 4 + Econst / 2) (d := 1) (e := 5)
    (N := (Bcount ⌊x⌋₊ : ℝ)) hx (by linarith) (by norm_num)
    (by have := counting_real_B hx; linarith)
  linarith

/-- Theorem `thm:counting2`: `A(x) ≥ (3 + C₁) log₂ x - O(log log x)`. -/
theorem counting2_real_asymp_A {x : ℝ} (hx : 16 ≤ x) :
    (3 + C1const) * Real.logb 2 x - 3 * Real.logb 2 (Real.logb 2 x) -
        (2 * (3 + C1const) + 10) ≤ (Acount ⌊x⌋₊ : ℝ) :=
  real_reduce (c := 3 + C1const) (d := 3) (e := 10) hx
    (by have := C1const_nonneg; linarith) (by norm_num) (counting2_real_A hx)

/-- Theorem `thm:counting2`: `B(x) ≥ (5/4 + E/2 + C₂) log₂ x - O(log log x)`. -/
theorem counting2_real_asymp_B {x : ℝ} (hx : 16 ≤ x) :
    (5 / 4 + Econst / 2 + C2const) * Real.logb 2 x - 3 * Real.logb 2 (Real.logb 2 x) -
        (2 * (5 / 4 + Econst / 2 + C2const) + 9) ≤ (Bcount ⌊x⌋₊ : ℝ) :=
  real_reduce (c := 5 / 4 + Econst / 2 + C2const) (d := 3) (e := 9) hx
    (by have := Econst_nonneg; have := C2const_nonneg; linarith) (by norm_num)
    (counting2_real_B hx)

end SequenceNicolas.Counting
