module

public import Mathlib
public import SequenceNicolas.PrimesBase

@[expose] public section

/-!
# The analogue for an arbitrary prime: `prop:Fp`

Over `𝔽_p[X]`, the exponent of `1 - X` in `(1 - X)(1 - X^2) ⋯ (1 - X^n)` is `c_p(n)`.
"The exponent of `P` in `A` is `e`" is expressed as `P^e ∣ A ∧ ¬ P^(e+1) ∣ A`.
-/

namespace SequenceNicolas.Primes

open Polynomial

/-- `(1 - X)(1 - X^2) ⋯ (1 - X^n)` over `𝔽_p`. -/
noncomputable def Fpoly (p n : ℕ) : (ZMod p)[X] := ∏ k ∈ Finset.range n, (1 - X ^ (k + 1))

/-- `e` is the exponent of `P` in `A`. -/
def Exact {R : Type*} [CommRing R] (P : R) (e : ℕ) (A : R) : Prop :=
  P ^ e ∣ A ∧ ¬ P ^ (e + 1) ∣ A

theorem Exact_mul {R : Type*} [CommRing R] [IsDomain R] {P A B : R} (hP : Prime P) {a b : ℕ}
    (hA : Exact P a A) (hB : Exact P b B) : Exact P (a + b) (A * B) := by
  obtain ⟨⟨A', hA'⟩, hA2⟩ := hA
  obtain ⟨⟨B', hB'⟩, hB2⟩ := hB
  have hA'n : ¬ P ∣ A' := fun h => hA2 (by rw [hA', pow_succ]; exact mul_dvd_mul_left _ h)
  have hB'n : ¬ P ∣ B' := fun h => hB2 (by rw [hB', pow_succ]; exact mul_dvd_mul_left _ h)
  have hAB : A * B = P ^ (a + b) * (A' * B') := by
    rw [hA', hB', pow_add]; ring
  refine ⟨⟨A' * B', hAB⟩, ?_⟩
  rintro ⟨c, hc⟩
  have h1 : P ^ (a + b) * (A' * B') = P ^ (a + b) * (P * c) := by
    rw [← hAB, hc, pow_succ]; ring
  have h2 : A' * B' = P * c := mul_left_cancel₀ (pow_ne_zero _ hP.ne_zero) h1
  rcases hP.dvd_or_dvd ⟨c, h2⟩ with h | h
  · exact hA'n h
  · exact hB'n h

theorem Exact_one {R : Type*} [CommRing R] [IsDomain R] {P : R} (hP : Prime P) :
    Exact P 0 1 := by
  refine ⟨by simp, ?_⟩
  rw [zero_add, pow_one]
  exact hP.not_dvd_one

theorem Exact_pow {R : Type*} [CommRing R] [IsDomain R] {P A : R} (hP : Prime P) {a : ℕ}
    (hA : Exact P a A) (m : ℕ) : Exact P (a * m) (A ^ m) := by
  induction m with
  | zero =>
    rw [mul_zero, pow_zero]
    exact Exact_one hP
  | succ m ih =>
    rw [mul_add, mul_one, pow_succ]
    exact Exact_mul hP ih hA

variable {p : ℕ} [hp : Fact p.Prime]

theorem prime_one_sub_X : Prime (1 - X : (ZMod p)[X]) := by
  have h := (Polynomial.prime_X_sub_C (1 : ZMod p)).neg
  have e : -(X - C (1 : ZMod p)) = 1 - X := by rw [C_1, neg_sub]
  rw [e] at h
  exact h

theorem exact_geom {k : ℕ} (hk : ¬ p ∣ k) :
    Exact (1 - X : (ZMod p)[X]) 1 (1 - X ^ k) := by
  have hP : Prime (1 - X : (ZMod p)[X]) := prime_one_sub_X
  have hgs : (1 - X ^ k : (ZMod p)[X]) = (∑ i ∈ Finset.range k, X ^ i) * (1 - X) :=
    (geom_sum_mul_neg X k).symm
  have hQ : ¬ (1 - X : (ZMod p)[X]) ∣ ∑ i ∈ Finset.range k, X ^ i := by
    rintro ⟨c, hc⟩
    have h1 := congrArg (Polynomial.eval 1) hc
    simp [eval_finsetSum] at h1
    exact hk ((CharP.cast_eq_zero_iff (ZMod p) p k).1 h1)
  refine ⟨⟨∑ i ∈ Finset.range k, X ^ i, ?_⟩, ?_⟩
  · rw [pow_one]
    exact hgs.trans (mul_comm _ _)
  · rintro ⟨c, hc⟩
    rw [hgs] at hc
    have h2 : (1 - X : (ZMod p)[X]) * (∑ i ∈ Finset.range k, X ^ i) =
        (1 - X) * ((1 - X) * c) := by
      linear_combination hc
    have h3 := mul_left_cancel₀ hP.ne_zero h2
    exact hQ ⟨c, h3⟩

theorem exact_term {k : ℕ} (hk : 1 ≤ k) :
    Exact (1 - X : (ZMod p)[X]) (p ^ padicValNat p k) (1 - X ^ k) := by
  obtain ⟨e, k', hk', hke⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : k ≠ 0) p hp.out.one_lt.ne'
  have hk'0 : k' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hke
    omega
  have hval : padicValNat p k = e := by
    rw [hke, padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hk'0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hk', add_zero]
  have h1 : (1 - X ^ k' : (ZMod p)[X]) ^ (p ^ e) = 1 - X ^ k := by
    rw [sub_pow_char_pow, one_pow, ← pow_mul, hke, mul_comm]
  have := Exact_pow prime_one_sub_X (exact_geom (p := p) hk') (p ^ e)
  rw [h1, one_mul] at this
  rw [hval]
  exact this

theorem Fpoly_exact (n : ℕ) :
    Exact (1 - X : (ZMod p)[X]) (cp p n) (Fpoly p n) := by
  induction n with
  | zero =>
    have h : Fpoly p 0 = 1 := by simp [Fpoly]
    rw [cp_zero, h]
    exact Exact_one prime_one_sub_X
  | succ n ih =>
    have h := Exact_mul prime_one_sub_X ih (exact_term (p := p) (k := n + 1) (by omega))
    rw [← cp_succ] at h
    have e : Fpoly p (n + 1) = Fpoly p n * (1 - X ^ (n + 1)) := by
      unfold Fpoly
      rw [Finset.prod_range_succ]
    rw [e]
    exact h

/-- Proposition `prop:Fp`: `c_p(n)` is the exponent of `1 - X` in `(1 - X)⋯(1 - X^n)` over `𝔽_p`. -/
theorem prop_Fp (n : ℕ) :
    (1 - X : (ZMod p)[X]) ^ cp p n ∣ Fpoly p n ∧ ¬ (1 - X : (ZMod p)[X]) ^ (cp p n + 1) ∣ Fpoly p n :=
  Fpoly_exact n

/-- The exponent is unique, so it is `c_p(n)`. -/
theorem prop_Fp_unique {n e : ℕ} (h1 : (1 - X : (ZMod p)[X]) ^ e ∣ Fpoly p n)
    (h2 : ¬ (1 - X : (ZMod p)[X]) ^ (e + 1) ∣ Fpoly p n) : e = cp p n := by
  obtain ⟨a1, a2⟩ := Fpoly_exact (p := p) n
  rcases lt_trichotomy e (cp p n) with h | h | h
  · exact absurd ((pow_dvd_pow _ (by omega : e + 1 ≤ cp p n)).trans a1) h2
  · exact h
  · exact absurd ((pow_dvd_pow _ (by omega : cp p n + 1 ≤ e)).trans h1) a2

end SequenceNicolas.Primes
