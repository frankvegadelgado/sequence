module

public import Mathlib
public import SequenceNicolas.PrimesBase
public import SequenceNicolas.PrimesRep
public import SequenceNicolas.PrimesStep
public import SequenceNicolas.PrimesFamilies

@[expose] public section

/-!
# The analogue for an arbitrary prime: the counting consequence of `thm:primefamilies`

`ApCount p X = #{a ≤ X : a ∈ 𝓐_p}` and `BpCount p X = #{a ≤ X : a ∉ 𝓐_p}`. With
`X = (p^H - 1)/(p - 1) + H` the bounds read `A_p(X) ≥ H` and `B_p(X) ≥ H + ⌊H/2⌋` for `p` odd, and
`X` is of the order of `p^H`, that is `H` is about `log_p X`.
-/

namespace SequenceNicolas.Primes

open scoped Classical

/-- `A_p(X)`. -/
noncomputable def ApCount (p X : ℕ) : ℕ := ((Finset.range (X + 1)).filter (fun a => Ap p a)).card

/-- `B_p(X)`. -/
noncomputable def BpCount (p X : ℕ) : ℕ :=
  ((Finset.range (X + 1)).filter (fun a => ¬ Ap p a)).card

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
theorem gsum_succ (g : ℕ) : gsum p (g + 1) = gsum p g + p ^ g := by
  unfold gsum
  rw [Finset.sum_range_succ]

omit hp in
theorem gsum_le {g H : ℕ} (h : g ≤ H) : gsum p g ≤ gsum p H :=
  Finset.sum_le_sum_of_subset (fun _ hx => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) h))

theorem gf_strictMono : StrictMono (fun g => gsum p g + g) := by
  apply strictMono_nat_of_lt_succ
  intro g
  show gsum p g + g < gsum p (g + 1) + (g + 1)
  rw [gsum_succ]
  have := pow_pos hp.out.pos g
  omega

theorem gK_eq {g : ℕ} (hg : 1 ≤ g) : (p - 1) * (gsum p g - 1) + p = p ^ g := by
  obtain ⟨s, hs⟩ : ∃ s, gsum p g = s + 1 :=
    ⟨gsum p g - 1, by have := gsum_pos (p := p) hg; omega⟩
  have h := gsum_spec (p := p) g
  rw [hs, mul_add] at h
  rw [hs, Nat.add_sub_cancel]
  have := hp.out.one_lt
  omega

/-- `A_p(X) ≥ H` for `X = (p^H - 1)/(p - 1) + H`, from Theorem `thm:primefamilies` (1). -/
theorem primecount_A (H : ℕ) : H ≤ ApCount p (gsum p H + H) := by
  unfold ApCount
  have hmem : ∀ g ∈ Finset.Icc 1 H, gsum p g + g - 2 ∈
      (Finset.range (gsum p H + H + 1)).filter (fun a => Ap p a) := by
    intro g hg
    rw [Finset.mem_Icc] at hg
    have h1 := gsum_pos (p := p) hg.1
    have h2 := gsum_le (p := p) hg.2
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have h3 := (primefam_one (p := p) hg.1 (gK_eq hg.1)).2
    have h4 : gsum p g - 1 + g - 1 = gsum p g + g - 2 := by omega
    rw [h4] at h3
    exact h3
  have hinj : Set.InjOn (fun g => gsum p g + g - 2) (Finset.Icc 1 H : Set ℕ) := by
    intro a ha b hb hab
    have ha' : a ∈ Finset.Icc 1 H := by simpa using ha
    have hb' : b ∈ Finset.Icc 1 H := by simpa using hb
    rw [Finset.mem_Icc] at ha' hb'
    have h1 := gsum_pos (p := p) ha'.1
    have h2 := gsum_pos (p := p) hb'.1
    have hab' : gsum p a + a - 2 = gsum p b + b - 2 := hab
    exact gf_strictMono.injective (show gsum p a + a = gsum p b + b by omega)
  have h : (Finset.Icc 1 H).card ≤
      ((Finset.range (gsum p H + H + 1)).filter (fun a => Ap p a)).card :=
    Finset.card_le_card_of_injOn (fun g => gsum p g + g - 2)
      (fun a ha => hmem a (by simpa using ha)) hinj
  have h2 : (Finset.Icc 1 H).card = H := by simp
  omega

/-- `K = (p^g - 2p + 1)/(2(p - 1))`, with `g = 2h`. -/
def Kq (p g : ℕ) : ℕ := (p ^ g + 1 - 2 * p) / (2 * (p - 1))

theorem Kq_spec (hp2 : p ≠ 2) {h : ℕ} (hh : 1 ≤ h) :
    2 * ((p - 1) * Kq p (2 * h) + p) = p ^ (2 * h) + 1 := by
  have hp1 := hp.out.one_lt
  obtain ⟨K, hK⟩ := primefam_three_exists (p := p) hp2 (g := 2 * h) (by omega) ⟨h, two_mul h⟩
  have e0 : 2 * (p - 1) * K = 2 * ((p - 1) * K) := by ring
  have e : p ^ (2 * h) + 1 - 2 * p = 2 * (p - 1) * K := by omega
  have : Kq p (2 * h) = K := by
    unfold Kq
    rw [e, Nat.mul_div_cancel_left K (show 0 < 2 * (p - 1) by omega)]
  rw [this]
  exact hK

theorem Kq_lt (hp2 : p ≠ 2) {h h' : ℕ} (hh : 1 ≤ h) (hlt : h < h') :
    Kq p (2 * h) < Kq p (2 * h') := by
  have hp1 := hp.out.one_lt
  have s1 := Kq_spec (p := p) hp2 hh
  have s2 := Kq_spec (p := p) hp2 (by omega : 1 ≤ h')
  have hpow := pow_lt_pow_p (p := p) (by omega : 2 * h < 2 * h')
  by_contra hc
  push Not at hc
  have := Nat.mul_le_mul_left (p - 1) hc
  omega

theorem Kq_le_gsum (hp2 : p ≠ 2) {h : ℕ} (hh : 1 ≤ h) : Kq p (2 * h) ≤ gsum p (2 * h) := by
  have hp1 := hp.out.one_lt
  have s1 := Kq_spec (p := p) hp2 hh
  have s2 := gsum_spec (p := p) (2 * h)
  have : (p - 1) * Kq p (2 * h) ≤ (p - 1) * gsum p (2 * h) := by omega
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- `B_p(X) ≥ H + ⌊H/2⌋` for `p` odd, `X = (p^H - 1)/(p - 1) + H`, from Theorem `thm:primes` (3)
and Theorem `thm:primefamilies` (3). -/
theorem primecount_B (hp2 : p ≠ 2) (H : ℕ) : H + H / 2 ≤ BpCount p (gsum p H + H) := by
  unfold BpCount
  have hp1 := hp.out.one_lt
  obtain ⟨G, hG⟩ : ∃ G : Finset ℕ, G = (Finset.Icc 1 H).image (fun g => gsum p g + g - 1) :=
    ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Finset ℕ,
      E = (Finset.Icc 1 (H / 2)).image (fun h => Kq p (2 * h) + 2 * h - 1) := ⟨_, rfl⟩
  have hinjG : Set.InjOn (fun g => gsum p g + g - 1) (Finset.Icc 1 H : Set ℕ) := by
    intro a ha b hb hab
    have ha' : a ∈ Finset.Icc 1 H := by simpa using ha
    have hb' : b ∈ Finset.Icc 1 H := by simpa using hb
    rw [Finset.mem_Icc] at ha' hb'
    have h1 := gsum_pos (p := p) ha'.1
    have h2 := gsum_pos (p := p) hb'.1
    have hab' : gsum p a + a - 1 = gsum p b + b - 1 := hab
    exact gf_strictMono.injective (show gsum p a + a = gsum p b + b by omega)
  have hinjE : Set.InjOn (fun h => Kq p (2 * h) + 2 * h - 1) (Finset.Icc 1 (H / 2) : Set ℕ) := by
    intro a ha b hb hab
    have ha' : a ∈ Finset.Icc 1 (H / 2) := by simpa using ha
    have hb' : b ∈ Finset.Icc 1 (H / 2) := by simpa using hb
    rw [Finset.mem_Icc] at ha' hb'
    have hab' : Kq p (2 * a) + 2 * a - 1 = Kq p (2 * b) + 2 * b - 1 := hab
    rcases lt_trichotomy a b with h | h | h
    · have := Kq_lt (p := p) hp2 ha'.1 h
      omega
    · exact h
    · have := Kq_lt (p := p) hp2 hb'.1 h
      omega
  have hcG : G.card = H := by
    rw [hG, Finset.card_image_of_injOn hinjG]
    simp
  have hcE : E.card = H / 2 := by
    rw [hE, Finset.card_image_of_injOn hinjE]
    simp
  have hdisj : Disjoint G E := by
    rw [Finset.disjoint_left]
    intro a haG haE
    rw [hG, Finset.mem_image] at haG
    rw [hE, Finset.mem_image] at haE
    obtain ⟨g, hg, hga⟩ := haG
    obtain ⟨h, hh, hha⟩ := haE
    rw [Finset.mem_Icc] at hg hh
    have h1 := gsum_pos (p := p) hg.1
    have hc := primefam_three (p := p) (K := Kq p (2 * h)) (g := 2 * h) hp2 (by omega)
      (Kq_spec (p := p) hp2 hh.1)
    apply bp_gap_of (p := p) hg.1
    refine ⟨Kq p (2 * h), ?_⟩
    have := hc.2.1
    omega
  have hsub : G ∪ E ⊆ (Finset.range (gsum p H + H + 1)).filter (fun a => ¬ Ap p a) := by
    intro a ha
    rw [Finset.mem_union] at ha
    rw [Finset.mem_filter, Finset.mem_range]
    rcases ha with ha | ha
    · rw [hG, Finset.mem_image] at ha
      obtain ⟨g, hg, hga⟩ := ha
      rw [Finset.mem_Icc] at hg
      have h2 := gsum_le (p := p) hg.2
      have h3 := not_Ap_gap (p := p) hg.1
      rw [← hga]
      exact ⟨by omega, h3⟩
    · rw [hE, Finset.mem_image] at ha
      obtain ⟨h, hh, hha⟩ := ha
      rw [Finset.mem_Icc] at hh
      have hc := primefam_three (p := p) (K := Kq p (2 * h)) (g := 2 * h) hp2 (by omega)
        (Kq_spec (p := p) hp2 hh.1)
      have h2 := gsum_le (p := p) (by omega : 2 * h ≤ H)
      have h3 := Kq_le_gsum (p := p) hp2 hh.1
      rw [← hha]
      exact ⟨by omega, hc.2.2.1⟩
  have hcard : (G ∪ E).card = G.card + E.card := by
    exact Finset.card_union_of_disjoint hdisj
  have := Finset.card_le_card hsub
  omega

end SequenceNicolas.Primes
