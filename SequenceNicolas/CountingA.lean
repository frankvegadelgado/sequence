module

public import Mathlib
public import SequenceNicolas.CountBase
public import SequenceNicolas.Counting

@[expose] public section

/-!
# Theorem `thm:counting`, the bound for `A(x)`
-/

namespace SequenceNicolas.Counting

open SequenceNicolas.CountBase SequenceNicolas.Recursion

theorem kappa_le_logb {H κ : ℕ} (_hH : 1 ≤ H) (hκ : 2 ^ κ ≤ H) : (κ : ℝ) ≤ Real.logb 2 (H : ℝ) := by
  have h1 : ((2 : ℝ) ^ κ) ≤ (H : ℝ) := by exact_mod_cast hκ
  have h2 : Real.logb 2 ((2 : ℝ) ^ κ) ≤ Real.logb 2 (H : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) h1
  have h3 : Real.logb 2 ((2 : ℝ) ^ κ) = κ := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; ring
  linarith

/-- The sum bound of Step 3. -/
theorem members_real {H κ : ℕ} (hκ : κ ≤ H) (hHκ : H < 2 ^ (κ + 1)) :
    (H : ℝ) - κ - 3 ≤ ((∑ k ∈ Finset.range (κ + 1), (H - k) / 2 ^ (k + 1) : ℕ) : ℝ) := by
  have hterm : ∀ k ∈ Finset.range (κ + 1),
      ((H : ℝ) - k) * (1 / 2 : ℝ) ^ (k + 1) - 1 ≤ (((H - k) / 2 ^ (k + 1) : ℕ) : ℝ) := by
    intro k hk
    have hk' : k ≤ H := by
      have := Finset.mem_range.1 hk
      omega
    have h := nat_div_ge (H - k) (2 ^ (k + 1)) (by positivity)
    have e1 : (((H - k : ℕ)) : ℝ) = (H : ℝ) - k := by
      rw [Nat.cast_sub hk']
    have e2 : (((2 ^ (k + 1) : ℕ)) : ℝ) = (2 : ℝ) ^ (k + 1) := by push_cast; ring
    rw [e1, e2] at h
    have e3 : ((H : ℝ) - k) * (1 / 2 : ℝ) ^ (k + 1) = ((H : ℝ) - k) / 2 ^ (k + 1) := by
      rw [one_div, inv_pow]; ring
    rw [e3]
    exact h
  have hsum := Finset.sum_le_sum hterm
  rw [members_sum] at hsum
  have hq : (0 : ℝ) < (1 / 2 : ℝ) ^ (κ + 1) := by positivity
  have hHq : (H : ℝ) * (1 / 2 : ℝ) ^ (κ + 1) < 1 := by
    have h1 : (H : ℝ) < 2 ^ (κ + 1) := by exact_mod_cast hHκ
    have e : (1 / 2 : ℝ) ^ (κ + 1) = 1 / 2 ^ (κ + 1) := by rw [one_div_pow]
    rw [e, mul_one_div, div_lt_one (by positivity)]
    exact h1
  have h3 : 0 ≤ ((κ : ℝ) + 2) * (1 / 2 : ℝ) ^ (κ + 1) := by positivity
  push_cast at hsum ⊢
  nlinarith [hsum, hHq, h3]

/-- `A(n) ≥ 2H - κ - 3` for `2^{H+1} ≤ n`, `2^κ ≤ H < 2^{κ+1}`. -/
theorem A_real {n H κ : ℕ} (hn : 2 ^ (H + 1) ≤ n) (_hH : 1 ≤ H) (hκ : 2 ^ κ ≤ H)
    (hHκ : H < 2 ^ (κ + 1)) : 2 * (H : ℝ) - κ - 3 ≤ (Acount n : ℝ) := by
  have hκH : κ ≤ H := by
    have := nat_lt_two_pow κ
    omega
  have h1 := A_nat hn hκH
  have h2 := members_real hκH hHκ
  have h3 : ((H + ∑ k ∈ Finset.range (κ + 1), (H - k) / 2 ^ (k + 1) : ℕ) : ℝ)
      ≤ (Acount n : ℝ) := by exact_mod_cast h1
  push_cast at h2 h3
  linarith

/-- Theorem `thm:counting`, first bound: `A(n) ≥ 2H - log₂ H - 3` where `2^{H+1} ≤ n`, `H ≥ 3`. -/
theorem counting_A {n H : ℕ} (hn : 2 ^ (H + 1) ≤ n) (hH : 3 ≤ H) :
    2 * (H : ℝ) - Real.logb 2 (H : ℝ) - 3 ≤ (Acount n : ℝ) := by
  obtain ⟨κ, hκ1, hκ2⟩ : ∃ κ, 2 ^ κ ≤ H ∧ H < 2 ^ (κ + 1) :=
    ⟨Nat.log 2 H, Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) H⟩
  have h1 := A_real hn (by omega) hκ1 hκ2
  have h2 := kappa_le_logb (by omega) hκ1
  linarith

end SequenceNicolas.Counting
