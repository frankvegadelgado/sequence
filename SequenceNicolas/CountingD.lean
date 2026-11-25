module

public import Mathlib
public import SequenceNicolas.CountBase
public import SequenceNicolas.Counting
public import SequenceNicolas.CountingA
public import SequenceNicolas.CountingB
public import SequenceNicolas.CountingC

@[expose] public section

/-!
# Theorem `thm:counting2`: the explicit bounds
-/

namespace SequenceNicolas.Counting

open SequenceNicolas.CountBase SequenceNicolas.Recursion

theorem Hq_lt {H κ : ℕ} (hHκ : H < 2 ^ (κ + 1)) : (H : ℝ) * (1 / 2 : ℝ) ^ κ < 2 := by
  have h1 : (H : ℝ) < 2 ^ (κ + 1) := by exact_mod_cast hHκ
  have e' : (1 / 2 : ℝ) ^ κ = 2 / 2 ^ (κ + 1) := by
    rw [one_div_pow, pow_succ]
    field_simp
  rw [e', mul_div_assoc', div_lt_iff₀ (by positivity)]
  nlinarith [h1]

theorem s2_real {H κ : ℕ} (hκ : κ ≤ H) (hHκ : H < 2 ^ (κ + 1)) :
    C1const * (H : ℝ) - 4 - 2 * κ ≤
      ((∑ j ∈ Finset.range κ, (H - (j + 1)) / (2 ^ j + 1 + 1) : ℕ) : ℝ) := by
  have hterm : ∀ j ∈ Finset.range κ,
      (H : ℝ) * (1 / ((2 : ℝ) ^ j + 2)) - 2 ≤ (((H - (j + 1)) / (2 ^ j + 1 + 1) : ℕ) : ℝ) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have h := nat_div_ge (H - (j + 1)) (2 ^ j + 1 + 1) (by positivity)
    have e1 : (((H - (j + 1) : ℕ)) : ℝ) = (H : ℝ) - ((j : ℝ) + 1) := by
      rw [Nat.cast_sub (show j + 1 ≤ H by omega)]
      push_cast; ring
    have e2 : (((2 ^ j + 1 + 1 : ℕ)) : ℝ) = (2 : ℝ) ^ j + 2 := by
      push_cast; ring
    rw [e1, e2] at h
    have hx : (0 : ℝ) < (2 : ℝ) ^ j + 2 := by positivity
    have hjx : ((j : ℝ) + 1) ≤ (2 : ℝ) ^ j + 2 := by
      have h0 := nat_lt_two_pow j
      have h0' : (j : ℝ) < 2 ^ j := by exact_mod_cast h0
      linarith
    have hkey : ((H : ℝ) - ((j : ℝ) + 1)) / ((2 : ℝ) ^ j + 2)
        = (H : ℝ) * (1 / ((2 : ℝ) ^ j + 2)) - ((j : ℝ) + 1) / ((2 : ℝ) ^ j + 2) := by
      rw [mul_one_div, ← sub_div]
    have hle : ((j : ℝ) + 1) / ((2 : ℝ) ^ j + 2) ≤ 1 := by
      rw [div_le_one hx]
      exact hjx
    linarith
  have hsum := Finset.sum_le_sum hterm
  have e : ∑ j ∈ Finset.range κ, ((H : ℝ) * (1 / ((2 : ℝ) ^ j + 2)) - 2)
      = (H : ℝ) * ∑ j ∈ Finset.range κ, 1 / ((2 : ℝ) ^ j + 2) - 2 * κ := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    ring
  rw [e] at hsum
  have hC := C1_tail κ
  have hq := Hq_lt hHκ
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_left (show C1const - 2 * 1 * (1 / 2 : ℝ) ^ κ ≤
      ∑ j ∈ Finset.range κ, 1 / ((2 : ℝ) ^ j + 2) by linarith) hH0
  push_cast at hsum ⊢
  nlinarith [hsum, hm, hq]

theorem s3_real {H κ : ℕ} (hκ : κ + 1 ≤ H) (hHκ : H < 2 ^ (κ + 1 + 1)) :
    C2const * (H : ℝ) - 4 - 2 * κ ≤
      ((∑ j ∈ Finset.range κ, (H - (j + 2)) / (2 ^ (j + 1) + 1) : ℕ) : ℝ) := by
  have hterm : ∀ j ∈ Finset.range κ,
      (H : ℝ) * (1 / ((2 : ℝ) ^ (j + 1) + 1)) - 2
        ≤ (((H - (j + 2)) / (2 ^ (j + 1) + 1) : ℕ) : ℝ) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have h := nat_div_ge (H - (j + 2)) (2 ^ (j + 1) + 1) (by positivity)
    have e1 : (((H - (j + 2) : ℕ)) : ℝ) = (H : ℝ) - ((j : ℝ) + 2) := by
      rw [Nat.cast_sub (show j + 2 ≤ H by omega)]
      push_cast; ring
    have e2 : (((2 ^ (j + 1) + 1 : ℕ)) : ℝ) = (2 : ℝ) ^ (j + 1) + 1 := by
      push_cast; ring
    rw [e1, e2] at h
    have hx : (0 : ℝ) < (2 : ℝ) ^ (j + 1) + 1 := by positivity
    have hjx : ((j : ℝ) + 2) ≤ (2 : ℝ) ^ (j + 1) + 1 := by
      have h0 := nat_lt_two_pow (j + 1)
      have h0' : ((j : ℝ) + 1) < 2 ^ (j + 1) := by exact_mod_cast h0
      linarith
    have hkey : ((H : ℝ) - ((j : ℝ) + 2)) / ((2 : ℝ) ^ (j + 1) + 1)
        = (H : ℝ) * (1 / ((2 : ℝ) ^ (j + 1) + 1)) - ((j : ℝ) + 2) / ((2 : ℝ) ^ (j + 1) + 1) := by
      rw [mul_one_div, ← sub_div]
    have hle : ((j : ℝ) + 2) / ((2 : ℝ) ^ (j + 1) + 1) ≤ 1 := by
      rw [div_le_one hx]
      exact hjx
    linarith
  have hsum := Finset.sum_le_sum hterm
  have e : ∑ j ∈ Finset.range κ, ((H : ℝ) * (1 / ((2 : ℝ) ^ (j + 1) + 1)) - 2)
      = (H : ℝ) * ∑ j ∈ Finset.range κ, 1 / ((2 : ℝ) ^ (j + 1) + 1) - 2 * κ := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    ring
  rw [e] at hsum
  have hC := C2_tail κ
  have hq := Hq_lt hHκ
  have hp : (1 / 2 : ℝ) ^ κ = 2 * (1 / 2 : ℝ) ^ (κ + 1) := by ring
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_left (show C2const - 2 * (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ κ ≤
      ∑ j ∈ Finset.range κ, 1 / ((2 : ℝ) ^ (j + 1) + 1) by linarith) hH0
  push_cast at hsum ⊢
  rw [hp] at hm
  nlinarith [hsum, hm, hq]

/-- Theorem `thm:counting2`, first bound. -/
theorem counting2_A {n H : ℕ} (hn : 2 ^ (H + 1) ≤ n) (hH : 3 ≤ H) :
    (3 + C1const) * (H : ℝ) - 3 * Real.logb 2 (H : ℝ) - 10 ≤ (Acount n : ℝ) := by
  obtain ⟨κ, hκ1, hκ2⟩ : ∃ κ, 2 ^ κ ≤ H ∧ H < 2 ^ (κ + 1) :=
    ⟨Nat.log 2 H, Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) H⟩
  have hκH : κ ≤ H := by
    have := nat_lt_two_pow κ
    omega
  have h1 := A2_nat hn hH hκH
  have h2 := members_real hκH hκ2
  have h3 := s2_real hκH hκ2
  have h4 := kappa_le_logb (by omega) hκ1
  have h5 : (((H + ∑ k ∈ Finset.range (κ + 1), (H - k) / 2 ^ (k + 1)) + (H - 3) +
      ∑ j ∈ Finset.range κ, (H - (j + 1)) / (2 ^ j + 1 + 1) : ℕ) : ℝ) ≤ (Acount n : ℝ) := by
    exact_mod_cast h1
  have h6 : (((H - 3 : ℕ)) : ℝ) = (H : ℝ) - 3 := by
    rw [Nat.cast_sub hH]
    norm_num
  push_cast at h2 h3 h5
  rw [h6] at h5
  nlinarith [h2, h3, h4, h5]

/-- Theorem `thm:counting2`, second bound. -/
theorem counting2_B {n H : ℕ} (hn : 2 ^ (H + 1) ≤ n) (hH : 3 ≤ H) :
    (5 / 4 + Econst / 2 + C2const) * (H : ℝ) - 3 * Real.logb 2 (H : ℝ) - 9 ≤ (Bcount n : ℝ) := by
  obtain ⟨κ, hκ1, hκ2⟩ : ∃ κ, 2 ^ κ ≤ H ∧ H < 2 ^ (κ + 1) :=
    ⟨Nat.log 2 H, Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) H⟩
  have hκH : κ ≤ H := by
    have := nat_lt_two_pow κ
    omega
  have hκ0 : 1 ≤ κ := by
    by_contra hc
    have h0 : κ = 0 := by omega
    rw [h0] at hκ2
    norm_num at hκ2
    omega
  obtain ⟨κ', rfl⟩ : ∃ κ', κ = κ' + 1 := ⟨κ - 1, by omega⟩
  have e1 : κ' + 1 - 1 = κ' := by omega
  have h1 := B2_nat hn hH hκH
  rw [e1] at h1
  have h2 := n1_real hκH hκ2
  have h3 := n2_real hH
  have h4 := s3_real (H := H) (κ := κ') hκH hκ2
  have h5 := kappa_le_logb (by omega) hκ1
  have h6 : ((H + ((∑ j ∈ Finset.range (κ' + 1), (H - (j + 1)) / (2 * (2 ^ (j + 1) - 1))) +
      ((H - 3) / 4 + 1)) + ∑ j ∈ Finset.range κ', (H - (j + 2)) / (2 ^ (j + 1) + 1) : ℕ) : ℝ)
      ≤ (Bcount n : ℝ) := by exact_mod_cast h1
  push_cast at h2 h3 h4 h5 h6
  nlinarith [h2, h3, h4, h5, h6]

end SequenceNicolas.Counting
