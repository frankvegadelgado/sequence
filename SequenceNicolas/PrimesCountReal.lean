module

public import Mathlib
public import SequenceNicolas.PrimesBase
public import SequenceNicolas.PrimesRep
public import SequenceNicolas.PrimesCount

@[expose] public section

/-!
# The counting consequence of `thm:primefamilies` for a real argument

`A_p(x) = ApCount p ⌊x⌋₊` and `B_p(x) = BpCount p ⌊x⌋₊`:
`A_p(x) ≥ log_p x - 2` for every prime `p`, and `B_p(x) ≥ (3/2) log_p x - 7/2` for odd `p`,
for every real `x ≥ p`.
-/

namespace SequenceNicolas.Primes

open scoped Classical

variable {p : ℕ} [hp : Fact p.Prime]

/-- `H = ⌊log_p x⌋ - 1`. -/
noncomputable def Hp (p : ℕ) (x : ℝ) : ℕ := ⌊Real.logb (p : ℝ) x⌋₊ - 1

theorem gsum_le_pow (H : ℕ) : gsum p H + H ≤ p ^ (H + 1) := by
  have hp2 := hp.out.two_le
  have h1 := gsum_spec (p := p) H
  have h2 : gsum p H ≤ (p - 1) * gsum p H := Nat.le_mul_of_pos_left _ (by omega)
  have h3 := lt_pow' hp2 H
  have h4 : p ^ (H + 1) = p ^ H * p := pow_succ _ _
  have h5 : p ^ H * 2 ≤ p ^ H * p := Nat.mul_le_mul_left _ hp2
  omega

theorem Hp_facts {x : ℝ} (hx : (p : ℝ) ≤ x) :
    gsum p (Hp p x) + Hp p x ≤ ⌊x⌋₊ ∧ Real.logb (p : ℝ) x - 2 < (Hp p x : ℝ) := by
  have hb : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  have hpos : 0 < x := by linarith
  have hlb : 0 ≤ Real.logb (p : ℝ) x := Real.logb_nonneg hb (by linarith)
  have h1 : (1 : ℝ) ≤ Real.logb (p : ℝ) x := by
    rw [Real.le_logb_iff_rpow_le hb hpos, Real.rpow_one]
    exact hx
  have hL1 : 1 ≤ ⌊Real.logb (p : ℝ) x⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  have hLle : ((⌊Real.logb (p : ℝ) x⌋₊ : ℕ) : ℝ) ≤ Real.logb (p : ℝ) x := Nat.floor_le hlb
  have hLlt : Real.logb (p : ℝ) x < ((⌊Real.logb (p : ℝ) x⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  unfold Hp
  obtain ⟨L, hL⟩ : ∃ L, L = ⌊Real.logb (p : ℝ) x⌋₊ := ⟨_, rfl⟩
  rw [← hL] at hL1 hLle hLlt ⊢
  have hHL : (((L - 1 : ℕ)) : ℝ) = (L : ℝ) - 1 := by
    rw [Nat.cast_sub hL1]
    norm_num
  have hpow : (p : ℝ) ^ L ≤ x := by
    have := (Real.le_logb_iff_rpow_le hb hpos).1 hLle
    rwa [Real.rpow_natCast] at this
  refine ⟨?_, by rw [hHL]; linarith⟩
  have e : L - 1 + 1 = L := by omega
  have h2 := gsum_le_pow (p := p) (L - 1)
  have h3 : p ^ (L - 1 + 1) ≤ ⌊x⌋₊ := by
    rw [e]
    exact Nat.le_floor (by push_cast; exact hpow)
  omega

omit hp in
theorem ApCount_mono {X Y : ℕ} (h : X ≤ Y) : ApCount p X ≤ ApCount p Y := by
  unfold ApCount
  apply Finset.card_le_card
  intro a ha
  rw [Finset.mem_filter, Finset.mem_range] at ha ⊢
  exact ⟨by omega, ha.2⟩

omit hp in
theorem BpCount_mono {X Y : ℕ} (h : X ≤ Y) : BpCount p X ≤ BpCount p Y := by
  unfold BpCount
  apply Finset.card_le_card
  intro a ha
  rw [Finset.mem_filter, Finset.mem_range] at ha ⊢
  exact ⟨by omega, ha.2⟩

/-- Theorem `thm:primefamilies`, counting statement for `A_p`: `A_p(x) ≥ log_p x - 2`. -/
theorem primecount_real_A {x : ℝ} (hx : (p : ℝ) ≤ x) :
    Real.logb (p : ℝ) x - 2 ≤ (ApCount p ⌊x⌋₊ : ℝ) := by
  obtain ⟨h1, h2⟩ := Hp_facts (p := p) hx
  have h3 : Hp p x ≤ ApCount p ⌊x⌋₊ :=
    (primecount_A (p := p) (Hp p x)).trans (ApCount_mono h1)
  have h4 : (Hp p x : ℝ) ≤ (ApCount p ⌊x⌋₊ : ℝ) := by exact_mod_cast h3
  linarith

/-- Theorem `thm:primefamilies`, counting statement for `B_p`, `p` odd:
`B_p(x) ≥ (3/2) log_p x - 7/2`. -/
theorem primecount_real_B (hp2 : p ≠ 2) {x : ℝ} (hx : (p : ℝ) ≤ x) :
    3 / 2 * Real.logb (p : ℝ) x - 7 / 2 ≤ (BpCount p ⌊x⌋₊ : ℝ) := by
  obtain ⟨h1, h2⟩ := Hp_facts (p := p) hx
  have h3 : Hp p x + Hp p x / 2 ≤ BpCount p ⌊x⌋₊ :=
    (primecount_B (p := p) hp2 (Hp p x)).trans (BpCount_mono h1)
  have h4 : 3 * Hp p x ≤ 2 * BpCount p ⌊x⌋₊ + 1 := by omega
  have h5 : (3 : ℝ) * (Hp p x : ℝ) ≤ 2 * (BpCount p ⌊x⌋₊ : ℝ) + 1 := by exact_mod_cast h4
  linarith

end SequenceNicolas.Primes
