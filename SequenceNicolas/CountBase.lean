module

public import Mathlib

@[expose] public section

/-!
# Real-analysis estimates for the counting bounds

Closed forms for the finite sums and the tail estimate for the constants
`E = ∑_{i ≥ 1} 1/(2^i - 1)`, `C₁ = ∑_{k ≥ 0} 1/(2^k + 2)`, `C₂ = ∑_{k ≥ 1} 1/(2^k + 1)`
used in Theorems `thm:counting` and `thm:counting2`.
-/

namespace SequenceNicolas.CountBase

/-- `⌊a/b⌋ ≥ a/b - 1`. -/
theorem nat_div_ge (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b - 1 ≤ ((a / b : ℕ) : ℝ) := by
  have h1 : a < b * (a / b + 1) := by
    have := Nat.lt_mul_div_succ a hb
    exact this
  have h2 : (a : ℝ) < b * (((a / b : ℕ) : ℝ) + 1) := by exact_mod_cast h1
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h3 : (a : ℝ) / b < ((a / b : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hb']
    nlinarith [h2]
  linarith

/-- `∑_{k=0}^{n} ((H - k)/2^{k+1} - 1)`. -/
theorem members_sum (H : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), ((H - k) * (1 / 2 : ℝ) ^ (k + 1) - 1)
      = H * (1 - (1 / 2 : ℝ) ^ (n + 1)) - (1 - ((n : ℝ) + 2) * (1 / 2 : ℝ) ^ (n + 1))
        - ((n : ℝ) + 1) := by
  induction n with
  | zero => simp only [zero_add, Finset.sum_range_one, Nat.cast_zero]; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- `∑_{i=1}^{n} i / 2^i ≤ 2`, in the indexing `i = j + 1`. -/
theorem ii_sum (n : ℕ) :
    ∑ j ∈ Finset.range n, ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ (j + 1)
      = 2 - ((n : ℝ) + 2) * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem ii_sum_le (n : ℕ) :
    ∑ j ∈ Finset.range n, ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ (j + 1) ≤ 2 := by
  rw [ii_sum]
  have : 0 ≤ ((n : ℝ) + 2) * (1 / 2 : ℝ) ^ n := by positivity
  linarith

/-- Tail estimate: if `0 ≤ f i ≤ c (1/2)^i`, then `∑' f - ∑_{i<n} f ≤ 2 c (1/2)^n`. -/
theorem tail_le (f : ℕ → ℝ) (c : ℝ) (_hc : 0 ≤ c) (hf0 : ∀ i, 0 ≤ f i)
    (hfg : ∀ i, f i ≤ c * (1 / 2 : ℝ) ^ i) (n : ℕ) :
    Summable f ∧ (∑' i, f i) - ∑ i ∈ Finset.range n, f i ≤ 2 * c * (1 / 2 : ℝ) ^ n := by
  have hg0 : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ i) := summable_geometric_two
  have hg : Summable (fun i : ℕ => c * (1 / 2 : ℝ) ^ i) := hg0.mul_left c
  have hs : Summable f := Summable.of_nonneg_of_le hf0 hfg hg
  refine ⟨hs, ?_⟩
  have h1 : ∑ i ∈ Finset.range n, f i + ∑' i, f (i + n) = ∑' i, f i := by
    exact Summable.sum_add_tsum_nat_add n hs
  have hs2 : Summable (fun i => f (i + n)) := (summable_nat_add_iff n).2 hs
  have hg2 : Summable (fun i : ℕ => c * (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ i) := hg0.mul_left _
  have hle : ∑' i, f (i + n) ≤ ∑' i : ℕ, c * (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ i := by
    apply Summable.tsum_le_tsum _ hs2 hg2
    intro i
    have := hfg (i + n)
    calc f (i + n) ≤ c * (1 / 2 : ℝ) ^ (i + n) := this
      _ = c * (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ i := by rw [pow_add]; ring
  have h2 : ∑' i : ℕ, c * (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ i = c * (1 / 2 : ℝ) ^ n * 2 := by
    rw [tsum_mul_left, tsum_geometric_two]
  linarith

/-- `E = ∑_{i ≥ 1} 1/(2^i - 1)`, indexed by `i ↦ 1/(2^{i+1} - 1)`. -/
noncomputable def Econst : ℝ := ∑' i : ℕ, 1 / ((2 : ℝ) ^ (i + 1) - 1)

/-- `C₁ = ∑_{k ≥ 0} 1/(2^k + 2)`. -/
noncomputable def C1const : ℝ := ∑' k : ℕ, 1 / ((2 : ℝ) ^ k + 2)

/-- `C₂ = ∑_{k ≥ 1} 1/(2^k + 1)`, indexed by `k ↦ 1/(2^{k+1} + 1)`. -/
noncomputable def C2const : ℝ := ∑' k : ℕ, 1 / ((2 : ℝ) ^ (k + 1) + 1)

theorem fE_nonneg (i : ℕ) : 0 ≤ 1 / ((2 : ℝ) ^ (i + 1) - 1) := by
  have : (2 : ℝ) ≤ 2 ^ (i + 1) := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (i + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  apply div_nonneg (by norm_num)
  linarith

theorem fE_le (i : ℕ) : 1 / ((2 : ℝ) ^ (i + 1) - 1) ≤ 1 * (1 / 2 : ℝ) ^ i := by
  have h2 : (2 : ℝ) ^ i ≥ 1 := one_le_pow₀ (by norm_num)
  have hp : (2 : ℝ) ^ (i + 1) = 2 * 2 ^ i := by ring
  have hpos : (0 : ℝ) < 2 ^ (i + 1) - 1 := by linarith
  rw [one_mul, one_div_le (by linarith) (by positivity)]
  have e3 : 1 / (1 / 2 : ℝ) ^ i = 2 ^ i := by simp
  rw [e3]
  linarith

theorem E_tail (n : ℕ) :
    Econst - ∑ i ∈ Finset.range n, 1 / ((2 : ℝ) ^ (i + 1) - 1) ≤ 2 * 1 * (1 / 2 : ℝ) ^ n :=
  (tail_le (fun i => 1 / ((2 : ℝ) ^ (i + 1) - 1)) 1 (by norm_num) fE_nonneg fE_le n).2

theorem E_summable : Summable (fun i : ℕ => 1 / ((2 : ℝ) ^ (i + 1) - 1)) :=
  (tail_le (fun i => 1 / ((2 : ℝ) ^ (i + 1) - 1)) 1 (by norm_num) fE_nonneg fE_le 0).1

theorem f1_nonneg (k : ℕ) : 0 ≤ 1 / ((2 : ℝ) ^ k + 2) := by positivity

theorem f1_le (k : ℕ) : 1 / ((2 : ℝ) ^ k + 2) ≤ 1 * (1 / 2 : ℝ) ^ k := by
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  rw [one_mul, one_div_le (by positivity) (by positivity)]
  have e3 : 1 / (1 / 2 : ℝ) ^ k = 2 ^ k := by simp
  rw [e3]
  linarith

theorem C1_tail (n : ℕ) :
    C1const - ∑ k ∈ Finset.range n, 1 / ((2 : ℝ) ^ k + 2) ≤ 2 * 1 * (1 / 2 : ℝ) ^ n :=
  (tail_le (fun k => 1 / ((2 : ℝ) ^ k + 2)) 1 (by norm_num) f1_nonneg f1_le n).2

theorem f2_nonneg (k : ℕ) : 0 ≤ 1 / ((2 : ℝ) ^ (k + 1) + 1) := by positivity

theorem f2_le (k : ℕ) : 1 / ((2 : ℝ) ^ (k + 1) + 1) ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k := by
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have hp : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
  have e : (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k = (1 / 2 : ℝ) ^ (k + 1) := by ring
  rw [e, one_div_le (by positivity) (by positivity)]
  have e3 : 1 / (1 / 2 : ℝ) ^ (k + 1) = 2 ^ (k + 1) := by simp
  rw [e3]
  linarith

theorem C2_tail (n : ℕ) :
    C2const - ∑ k ∈ Finset.range n, 1 / ((2 : ℝ) ^ (k + 1) + 1) ≤ 2 * (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n :=
  (tail_le (fun k => 1 / ((2 : ℝ) ^ (k + 1) + 1)) (1 / 2) (by norm_num) f2_nonneg f2_le n).2

theorem C1_summable : Summable (fun k : ℕ => 1 / ((2 : ℝ) ^ k + 2)) :=
  (tail_le (fun k => 1 / ((2 : ℝ) ^ k + 2)) 1 (by norm_num) f1_nonneg f1_le 0).1

theorem C2_summable : Summable (fun k : ℕ => 1 / ((2 : ℝ) ^ (k + 1) + 1)) :=
  (tail_le (fun k => 1 / ((2 : ℝ) ^ (k + 1) + 1)) (1 / 2) (by norm_num) f2_nonneg f2_le 0).1

/-! ### The decimal values of the constants -/

theorem E_tight : (1606695152 / 1000000000 : ℝ) < Econst ∧ Econst < 1606695153 / 1000000000 := by
  have h1 : ∑ i ∈ Finset.range 40, 1 / ((2 : ℝ) ^ (i + 1) - 1) ≤ Econst :=
    E_summable.sum_le_tsum _ (fun i _ => fE_nonneg i)
  have h2 := E_tail 40
  have h3 : (1606695152 / 1000000000 : ℝ) < ∑ i ∈ Finset.range 40, 1 / ((2 : ℝ) ^ (i + 1) - 1) := by
    norm_num [Finset.sum_range_succ]
  have h4 : (∑ i ∈ Finset.range 40, 1 / ((2 : ℝ) ^ (i + 1) - 1)) + 2 * 1 * (1 / 2 : ℝ) ^ 40
      < 1606695153 / 1000000000 := by
    norm_num [Finset.sum_range_succ]
  constructor <;> linarith

theorem C1_tight : (965583223 / 1000000000 : ℝ) < C1const ∧ C1const < 965583224 / 1000000000 := by
  have h1 : ∑ k ∈ Finset.range 40, 1 / ((2 : ℝ) ^ k + 2) ≤ C1const :=
    C1_summable.sum_le_tsum _ (fun k _ => f1_nonneg k)
  have h2 := C1_tail 40
  have h3 : (965583223 / 1000000000 : ℝ) < ∑ k ∈ Finset.range 40, 1 / ((2 : ℝ) ^ k + 2) := by
    norm_num [Finset.sum_range_succ]
  have h4 : (∑ k ∈ Finset.range 40, 1 / ((2 : ℝ) ^ k + 2)) + 2 * 1 * (1 / 2 : ℝ) ^ 40
      < 965583224 / 1000000000 := by
    norm_num [Finset.sum_range_succ]
  constructor <;> linarith

theorem C2_tight : (764499780 / 1000000000 : ℝ) < C2const ∧ C2const < 764499781 / 1000000000 := by
  have h1 : ∑ k ∈ Finset.range 40, 1 / ((2 : ℝ) ^ (k + 1) + 1) ≤ C2const :=
    C2_summable.sum_le_tsum _ (fun k _ => f2_nonneg k)
  have h2 := C2_tail 40
  have h3 : (764499780 / 1000000000 : ℝ) < ∑ k ∈ Finset.range 40, 1 / ((2 : ℝ) ^ (k + 1) + 1) := by
    norm_num [Finset.sum_range_succ]
  have h4 : (∑ k ∈ Finset.range 40, 1 / ((2 : ℝ) ^ (k + 1) + 1)) + 2 * (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ 40
      < 764499781 / 1000000000 := by
    norm_num [Finset.sum_range_succ]
  constructor <;> linarith

/-- `E = 1.6066951…` -/
theorem E_dec : (16066951 / 10000000 : ℝ) ≤ Econst ∧ Econst < 16066952 / 10000000 := by
  obtain ⟨h1, h2⟩ := E_tight
  constructor <;> linarith

/-- `C₁ = 0.9655832…` -/
theorem C1_dec : (9655832 / 10000000 : ℝ) ≤ C1const ∧ C1const < 9655833 / 10000000 := by
  obtain ⟨h1, h2⟩ := C1_tight
  constructor <;> linarith

/-- `C₂ = 0.7644997…` -/
theorem C2_dec : (7644997 / 10000000 : ℝ) ≤ C2const ∧ C2const < 7644998 / 10000000 := by
  obtain ⟨h1, h2⟩ := C2_tight
  constructor <;> linarith

/-- `5/4 + E/2 = 2.0533475…` -/
theorem constB_dec :
    (20533475 / 10000000 : ℝ) ≤ 5 / 4 + Econst / 2 ∧ 5 / 4 + Econst / 2 < 20533476 / 10000000 := by
  obtain ⟨h1, h2⟩ := E_tight
  constructor <;> linarith

/-- `3 + C₁ = 3.9655832…` -/
theorem const2A_dec :
    (39655832 / 10000000 : ℝ) ≤ 3 + C1const ∧ 3 + C1const < 39655833 / 10000000 := by
  obtain ⟨h1, h2⟩ := C1_tight
  constructor <;> linarith

/-- `5/4 + E/2 + C₂ = 2.8178473…` -/
theorem const2B_dec :
    (28178473 / 10000000 : ℝ) ≤ 5 / 4 + Econst / 2 + C2const ∧
      5 / 4 + Econst / 2 + C2const < 28178474 / 10000000 := by
  obtain ⟨h1, h2⟩ := E_tight
  obtain ⟨h3, h4⟩ := C2_tight
  constructor <;> linarith

end SequenceNicolas.CountBase
