module

public import Mathlib
public import SequenceNicolas.PrimesBase
public import SequenceNicolas.PrimesRep
public import SequenceNicolas.PrimesStep
public import SequenceNicolas.PrimesFamilies

@[expose] public section

/-!
# The analogue for an arbitrary prime: `thm:immediate`

`Imm p K` says that the exponent with candidate `K` is an immediate failure, that is
`w₀ > (p-1)K`, where `w₀ = p^g % u`, `u = (p-1)K + p`, `g = g(K)`.
-/

namespace SequenceNicolas.Primes

open scoped Classical

/-- The exponent with candidate `K` is an immediate failure: `w₀ > (p - 1) K`. -/
def Imm (p K : ℕ) : Prop := (p - 1) * K < p ^ gexp p K % ((p - 1) * K + p)

theorem imm_arith {s p P : ℕ} (hp1 : 2 ≤ p) :
    s < P % (s + p) ↔ ∃ j, 1 ≤ j ∧ j ≤ p - 1 ∧ (s + p) ∣ P + j := by
  have hu : 0 < s + p := by omega
  have hdm := Nat.div_add_mod P (s + p)
  have hr := Nat.mod_lt P hu
  generalize P / (s + p) = d at hdm
  generalize P % (s + p) = r at hdm hr ⊢
  constructor
  · intro h
    refine ⟨s + p - r, by omega, by omega, ?_⟩
    refine ⟨d + 1, ?_⟩
    rw [mul_add, mul_one]
    omega
  · rintro ⟨j, hj1, hj2, e, he⟩
    rcases (by omega : e ≤ d ∨ e = d + 1 ∨ d + 2 ≤ e) with h | h | h
    · have := Nat.mul_le_mul_left (s + p) h
      omega
    · subst h
      rw [mul_add, mul_one] at he
      omega
    · have := Nat.mul_le_mul_left (s + p) h
      rw [mul_add] at this
      omega

variable {p : ℕ} [hp : Fact p.Prime]

/-- Theorem `thm:immediate`, criterion. -/
theorem imm_iff (K : ℕ) :
    Imm p K ↔ ∃ j, 1 ≤ j ∧ j ≤ p - 1 ∧ ((p - 1) * K + p) ∣ p ^ gexp p K + j := by
  unfold Imm
  exact imm_arith hp.out.two_le

/-- Theorem `thm:immediate`, the range of `e`. -/
theorem imm_range {K j e : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ p - 1)
    (he : ((p - 1) * K + p) * e = p ^ gexp p K + j) : 2 ≤ e ∧ e ≤ p - 1 := by
  obtain ⟨c1, c2⟩ := cand_data (p := p) K
  have hp1 := hp.out.one_lt
  have e1 : (p - 1) * (K + 1) = (p - 1) * K + (p - 1) := by ring
  constructor
  · by_contra hc
    have h1 : ((p - 1) * K + p) * e ≤ ((p - 1) * K + p) * 1 :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · by_contra hc
    have h1 : ((p - 1) * K + p) * p ≤ ((p - 1) * K + p) * e :=
      Nat.mul_le_mul_left _ (by omega)
    have fA : p * ((p - 1) * K) = ((p - 1) * K) * p := mul_comm _ _
    have fB : p * (p - 1) = (p - 1) * p := mul_comm _ _
    have fC : (p - 1) * p + p = p * p := pm1 hp.out.one_lt.le p
    have fD : p * ((p - 1) * (K + 1)) = p * ((p - 1) * K) + p * (p - 1) := by
      rw [e1, mul_add]
    have fE : ((p - 1) * K + p) * p = ((p - 1) * K) * p + p * p := add_mul _ _ _
    omega

/-- No immediate failures for `p = 2`. -/
theorem imm_two (hp2 : p = 2) (K : ℕ) : ¬ Imm p K := by
  intro h
  obtain ⟨j, hj1, hj2, e, he⟩ := (imm_iff K).1 h
  have := imm_range hj1 hj2 he.symm
  omega

/-- Theorem `thm:immediate`: the triple `(g, e, j)` attached to an immediate failure. -/
theorem imm_triple {K : ℕ} (h : Imm p K) :
    ∃ e j, 2 ≤ e ∧ e ≤ p - 1 ∧ 1 ≤ j ∧ j ≤ p - 1 ∧
      ((p - 1) * K + p) * e = p ^ gexp p K + j ∧ p ≤ (p - 1) * K + p ∧
      (p - 1) * K + p ≤ p ^ gexp p K ∧ p ^ gexp p K ≤ p * ((p - 1) * (K + 1)) := by
  obtain ⟨j, hj1, hj2, e, he⟩ := (imm_iff K).1 h
  have hr := imm_range hj1 hj2 he.symm
  obtain ⟨c1, c2⟩ := cand_data (p := p) K
  exact ⟨e, j, hr.1, hr.2, hj1, hj2, he.symm, by omega, c1, c2⟩

/-- Theorem `thm:immediate`: the converse, from a triple to an immediate failure. -/
theorem imm_param {K g e j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ p - 1) (hg : 1 ≤ g)
    (h : ((p - 1) * K + p) * e = p ^ g + j) (hle : (p - 1) * K + p ≤ p ^ g)
    (hup : p ^ g ≤ p * ((p - 1) * (K + 1))) : gexp p K = g ∧ Imm p K := by
  have hp1 := hp.out.one_lt
  have e1 : (p - 1) * (K + 1) = (p - 1) * K + (p - 1) := by ring
  have hgx : gexp p K = g := by
    apply gexp_eq hg (by omega)
    intro n hn1 hn
    obtain ⟨g', hg'⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    have h1 : p ^ n ≤ p ^ g' := pow_le_pow_p (by omega)
    have h2 : p ^ (g' + 1) = p * p ^ g' := pow_succ' _ _
    rw [hg'] at hup
    rw [h2] at hup
    have h3 : p ^ g' ≤ (p - 1) * (K + 1) := Nat.le_of_mul_le_mul_left hup hp.out.pos
    omega
  refine ⟨hgx, ?_⟩
  refine (imm_iff K).2 ⟨j, hj1, hj2, ?_⟩
  rw [hgx]
  exact ⟨e, h.symm⟩

/-- Theorem `thm:immediate`, the case `p = 3`. -/
theorem imm_three (hp3 : p = 3) (K : ℕ) :
    Imm p K ↔ ∃ h, 1 ≤ h ∧ 4 * K + 5 = 3 ^ (2 * h) := by
  subst hp3
  constructor
  · intro hI
    obtain ⟨j, hj1, hj2, e, he⟩ := (imm_iff K).1 hI
    have hr := imm_range hj1 hj2 he.symm
    have he2 : e = 2 := by omega
    subst he2
    have hodd : Odd (3 ^ gexp 3 K) := Odd.pow (by decide)
    obtain ⟨r, hr'⟩ := hodd
    have hP : 4 * K + 5 = 3 ^ gexp 3 K := by omega
    have hg1 := (gexp_spec (p := 3) K).1
    rcases Nat.even_or_odd (gexp 3 K) with ⟨h, hh⟩ | ⟨h, hh⟩
    · refine ⟨h, by omega, ?_⟩
      rw [show 2 * h = gexp 3 K by omega]
      exact hP
    · exfalso
      have h9 : 9 ^ h % 4 = 1 := by
        rw [Nat.pow_mod]
        norm_num
      have h3 : 3 ^ (2 * h + 1) = 9 ^ h * 3 := by
        rw [pow_succ, pow_mul]
        norm_num
      rw [hh, h3] at hP
      omega
  · rintro ⟨h, h1, hK⟩
    have hc := primefam_three (p := 3) (K := K) (g := 2 * h) (by norm_num) (by omega)
      (by omega)
    unfold Imm
    rw [hc.1, hc.2.2.2]
    omega

/-- Theorem `thm:immediate`: at most `(p-1)(p-2)` immediate failures with a given `g`. -/
theorem imm_count (g : ℕ) (S : Finset ℕ) (hS : ∀ K ∈ S, gexp p K = g ∧ Imm p K) :
    S.card ≤ (p - 1) * (p - 2) := by
  have hp1 := hp.out.one_lt
  have hsub : S ⊆ ((Finset.Icc 2 (p - 1)) ×ˢ (Finset.Icc 1 (p - 1))).image
        (fun x : ℕ × ℕ => ((p ^ g + x.2) / x.1 - p) / (p - 1)) := by
    intro K hK
    obtain ⟨hgK, hI⟩ := hS K hK
    obtain ⟨j, hj1, hj2, e, he⟩ := (imm_iff K).1 hI
    have hr := imm_range hj1 hj2 he.symm
    rw [hgK] at he
    rw [Finset.mem_image]
    refine ⟨(e, j), ?_, ?_⟩
    · rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      exact ⟨⟨hr.1, hr.2⟩, ⟨hj1, hj2⟩⟩
    · show ((p ^ g + j) / e - p) / (p - 1) = K
      rw [he, Nat.mul_div_cancel _ (show 0 < e by omega), Nat.add_sub_cancel,
        Nat.mul_div_cancel_left K (show 0 < p - 1 by omega)]
  calc S.card
      ≤ (((Finset.Icc 2 (p - 1)) ×ˢ (Finset.Icc 1 (p - 1))).image
        (fun x : ℕ × ℕ => ((p ^ g + x.2) / x.1 - p) / (p - 1))).card := Finset.card_le_card hsub
    _ ≤ ((Finset.Icc 2 (p - 1)) ×ˢ (Finset.Icc 1 (p - 1))).card := Finset.card_image_le
    _ = (p - 1) * (p - 2) := by
      rw [Finset.card_product, Nat.card_Icc, Nat.card_Icc]
      have h1 : p - 1 + 1 - 2 = p - 2 := by omega
      have h2 : p - 1 + 1 - 1 = p - 1 := by omega
      rw [h1, h2, mul_comm]

end SequenceNicolas.Primes
