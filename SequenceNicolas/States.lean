module

public import Mathlib
public import SequenceNicolas.Core
public import SequenceNicolas.Recursion

@[expose] public section

/-!
# Successful states: symmetry, the forest and the bottom-up recursion

This module formalizes Proposition `prop:symmetry`, the preimage description of the map `Φ`
(Theorem `thm:forest` (2)), the forest property (Theorem `thm:forest` (3), without the counting
identities), the initial states (Theorem `thm:forest` (4)) and the pointwise form of
Theorem `thm:bottomup`.
-/

namespace SequenceNicolas.States

open SequenceNicolas.Recursion

/-! ### Proposition `prop:symmetry` -/

theorem no_one {T : Finset ℕ} {J : ℕ} (hT : T ⊆ Finset.Icc 1 J)
    (h8 : 8 ∣ ∑ j ∈ T, j * 2 ^ j) : 1 ∉ T := by
  intro h1
  have hdiv : 8 ∣ ∑ j ∈ T.erase 1, j * 2 ^ j := by
    apply Finset.dvd_sum
    intro j hj
    have hj1 : j ≠ 1 := (Finset.mem_erase.1 hj).1
    have hj2 : 1 ≤ j := (Finset.mem_Icc.1 (hT (Finset.mem_erase.1 hj).2)).1
    rcases (by omega : j = 2 ∨ 3 ≤ j) with rfl | h3
    · norm_num
    · have h : 2 ^ 3 ∣ 2 ^ j := pow_dvd_pow 2 h3
      have h8' : (8 : ℕ) ∣ 2 ^ j := by
        exact h
      exact Dvd.dvd.mul_left h8' j
  have hsplit := Finset.add_sum_erase T (fun j => j * 2 ^ j) h1
  simp only [one_mul, pow_one] at hsplit
  omega

theorem succ_symm_aux {J w : ℕ} (hJ : 2 ≤ J) (hw : w + 1 ≤ J) (h : Succ J w) :
    Succ J (J - 1 - w) := by
  obtain ⟨T, hT, hs⟩ := h
  have hX8 : 8 ∣ 2 ^ (J + 1) := by
    have h3 : 2 ^ 3 ∣ 2 ^ (J + 1) := pow_dvd_pow 2 (by omega)
    exact h3
  have h8 : 8 ∣ ∑ j ∈ T, j * 2 ^ j := by
    rw [hs]
    exact Dvd.dvd.mul_right hX8 w
  have h1 := no_one hT h8
  have hUsub : insert 1 T ⊆ Finset.Icc 1 J := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx'
    · exact Finset.mem_Icc.2 ⟨le_refl _, by omega⟩
    · exact hT hx'
  have hUsum : ∑ j ∈ insert 1 T, j * 2 ^ j = 2 + ∑ j ∈ T, j * 2 ^ j := by
    rw [Finset.sum_insert h1]
    norm_num
  have hsd : ∑ j ∈ Finset.Icc 1 J \ insert 1 T, j * 2 ^ j + ∑ j ∈ insert 1 T, j * 2 ^ j
      = ∑ j ∈ Finset.Icc 1 J, j * 2 ^ j := Finset.sum_sdiff hUsub
  refine ⟨Finset.Icc 1 J \ insert 1 T, fun x hx => (Finset.mem_sdiff.1 hx).1, ?_⟩
  have h2 := SequenceNicolas.Core.sum_j_two_pow J
  obtain ⟨d, hd⟩ : ∃ d, J = w + d + 1 := ⟨J - 1 - w, by omega⟩
  have e : J - 1 - w = d := by omega
  have hJX : J * 2 ^ (J + 1) = w * 2 ^ (J + 1) + d * 2 ^ (J + 1) + 2 ^ (J + 1) := by
    have : J * 2 ^ (J + 1) = (w + d + 1) * 2 ^ (J + 1) := by rw [← hd]
    rw [this]
    ring
  rw [e]
  nlinarith [hsd, hUsum, h2, hs, hJX]

/-- Proposition `prop:symmetry`: `w ∈ S_J` iff `J - 1 - w ∈ S_J`. -/
theorem succ_symm {J w : ℕ} (hJ : 1 ≤ J) (hw : w + 1 ≤ J) :
    Succ J w ↔ Succ J (J - 1 - w) := by
  rcases (by omega : J = 1 ∨ 2 ≤ J) with rfl | hJ2
  · have : w = 0 := by omega
    subst this
    exact Iff.rfl
  · constructor
    · exact succ_symm_aux hJ2 hw
    · intro h
      have := succ_symm_aux hJ2 (by omega : J - 1 - w + 1 ≤ J) h
      have e : J - 1 - (J - 1 - w) = w := by omega
      rw [e] at this
      exact this

/-! ### Theorem `thm:bottomup` (pointwise form) -/

/-- Theorem `thm:bottomup`: `w ∈ S_{m+1}` iff `w = (c + x (m+1))/2` with `c ∈ S_m` and `x ∈ {0,1}`.
For `m + 1` odd this is part (1) and for `m + 1` even it is part (2). -/
theorem bottomup_iff {m w : ℕ} :
    Succ (m + 1) w ↔ ∃ c x, Succ m c ∧ x ≤ 1 ∧ c + x * (m + 1) = 2 * w := by
  have hX : 0 < 2 ^ (m + 1) := by positivity
  have hX2 : 2 ^ (m + 1 + 1) = 2 * 2 ^ (m + 1) := by ring
  constructor
  · rintro ⟨T, hT, hs⟩
    by_cases hmT : m + 1 ∈ T
    · have hU := erase_sub hT
      have hsp := sum_erase_eq hmT
      have hle : (m + 1) * 2 ^ (m + 1) ≤ 2 ^ (m + 1) * (2 * w) := by
        have h1 : (m + 1) * 2 ^ (m + 1) ≤ ∑ j ∈ T, j * 2 ^ j := by
          rw [hsp]
          exact Nat.le_add_right _ _
        calc (m + 1) * 2 ^ (m + 1) ≤ ∑ j ∈ T, j * 2 ^ j := h1
          _ = 2 ^ (m + 1) * (2 * w) := by rw [hs, hX2]; ring
      have hle' : m + 1 ≤ 2 * w := by
        have h' : 2 ^ (m + 1) * (m + 1) ≤ 2 ^ (m + 1) * (2 * w) := by
          rw [mul_comm (2 ^ (m + 1))]
          exact hle
        exact Nat.le_of_mul_le_mul_left h' hX
      refine ⟨2 * w - (m + 1), 1, ⟨T.erase (m + 1), hU, ?_⟩, le_refl _, by omega⟩
      rw [hX2] at hs
      obtain ⟨c, hc⟩ : ∃ c, 2 * w = (m + 1) + c := ⟨2 * w - (m + 1), by omega⟩
      have e : 2 * w - (m + 1) = c := by omega
      rw [e]
      have hc2 : 2 ^ (m + 1) * (2 * w) = 2 ^ (m + 1) * ((m + 1) + c) := by rw [hc]
      nlinarith [hs, hsp, hc2]
    · refine ⟨2 * w, 0, ⟨T, not_mem_sub hT hmT, ?_⟩, by omega, by omega⟩
      rw [hX2] at hs
      nlinarith [hs]
  · rintro ⟨c, x, ⟨U, hU, hus⟩, hx, hcx⟩
    rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl
    · refine ⟨U, ?_, ?_⟩
      · intro j hj
        have := Finset.mem_Icc.1 (hU hj)
        exact Finset.mem_Icc.2 ⟨this.1, by omega⟩
      · rw [hus, hX2]
        have : c = 2 * w := by omega
        subst this
        ring
    · have hnot : m + 1 ∉ U := fun h => by
        have := (Finset.mem_Icc.1 (hU h)).2
        omega
      refine ⟨insert (m + 1) U, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj'
        · exact Finset.mem_Icc.2 ⟨by omega, le_refl _⟩
        · have := Finset.mem_Icc.1 (hU hj')
          exact Finset.mem_Icc.2 ⟨this.1, by omega⟩
      · rw [Finset.sum_insert hnot, hus, hX2]
        have hc2 : 2 ^ (m + 1) * (c + 1 * (m + 1)) = 2 ^ (m + 1) * (2 * w) := by rw [hcx]
        nlinarith [hc2]

/-! ### The map `Φ` and the forest (Theorem `thm:forest`) -/

/-- `Phi J w J' w'`: `(J, w)` is a state with `w ≥ 1` that does not fail and `Φ(J, w) = (J', w')`
(`J = J' + s`, `w' = 2^s w + s - J - 1`, with `s = t + 1` the integer of Theorem `thm:step`). -/
def Phi (J w J' w' : ℕ) : Prop :=
  IsState J w ∧ 1 ≤ w ∧ ∃ t, IsS J w (t + 1) ∧ 2 ^ t * w + (t + 1) ≠ J + 1 ∧
    J = J' + (t + 1) ∧ 2 ^ (t + 1) * w + (t + 1) = J + 1 + w'

/-- `Φ` is a partial function. -/
theorem phi_unique {J w J₁ w₁ J₂ w₂ : ℕ} (h₁ : Phi J w J₁ w₁) (h₂ : Phi J w J₂ w₂) :
    J₁ = J₂ ∧ w₁ = w₂ := by
  obtain ⟨_, _, t₁, hS₁, _, hJ₁, he₁⟩ := h₁
  obtain ⟨_, _, t₂, hS₂, _, hJ₂, he₂⟩ := h₂
  have := IsS_unique hS₁ hS₂
  have ht : t₁ = t₂ := by omega
  subst ht
  omega

/-- `Φ` lowers the first coordinate. -/
theorem phi_lt {J w J' w' : ℕ} (h : Phi J w J' w') : J' < J := by
  obtain ⟨_, _, t, _, _, hJ, _⟩ := h
  omega

/-- Theorem `thm:forest` (2): the states `(J, w)` with `Φ(J, w) = (J', w')` are exactly the
pairs `(J' + σ, u / 2^σ)` with `u = J' + 1 + w'` and `2^σ ∣ u`, `σ ≥ 1` (here `σ = t + 1`). -/
theorem phi_iff {J w J' w' : ℕ} (hst' : IsState J' w') :
    Phi J w J' w' ↔ ∃ t, J = J' + (t + 1) ∧ 2 ^ (t + 1) * w = J' + 1 + w' := by
  obtain ⟨hJ', hw'⟩ := hst'
  constructor
  · rintro ⟨_, _, t, _, _, hJ, he⟩
    exact ⟨t, hJ, by omega⟩
  · rintro ⟨t, hJ, heq⟩
    subst hJ
    have hP : 2 ^ (t + 1) * w = 2 * (2 ^ t * w) := by ring
    have hpos : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    have hw1 : 1 ≤ w := by
      by_contra hc
      have h0 : w = 0 := by omega
      subst h0
      rw [mul_zero] at heq
      omega
    have h1w : 1 * w ≤ 2 ^ t * w := Nat.mul_le_mul_right w hpos
    have hst : IsState (J' + (t + 1)) w := ⟨by omega, by omega⟩
    have hS : IsS (J' + (t + 1)) w (t + 1) :=
      (least_char hst hw1).2 ⟨by omega, by omega⟩
    exact ⟨hst, hw1, t, hS, by omega, rfl, by omega⟩

/-- A root is a state with `w = 0` or a failing state; a successful state either is a root `(J, 0)`
or is mapped by `Φ` to a successful state (Theorem `thm:forest` (3) and Theorem `thm:step`). -/
theorem succ_iff_phi {J w : ℕ} (hst : IsState J w) :
    Succ J w ↔ w = 0 ∨ ∃ J' w', Phi J w J' w' ∧ Succ J' w' := by
  rcases Nat.eq_zero_or_pos w with hw0 | hw
  · subst hw0
    exact ⟨fun _ => Or.inl rfl, fun _ => succ_zero J⟩
  · obtain ⟨s, hS, hsJ⟩ := exists_S hst hw
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by have := hS.1; omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, J = m + (t + 1) := ⟨J - (t + 1), by omega⟩
    have hm : 1 ≤ m := by omega
    obtain ⟨hfail, hok⟩ := step_main hst hw hS hm
    constructor
    · intro hsucc
      by_cases hnf : 2 ^ t * w + (t + 1) = m + (t + 1) + 1
      · exact absurd hsucc (hfail hnf)
      · obtain ⟨w', heq, hst', hiff⟩ := hok hnf
        refine Or.inr ⟨m, w', ?_, hiff.1 hsucc⟩
        exact ⟨hst, hw, t, hS, hnf, rfl, by omega⟩
    · rintro (h0 | ⟨J', w', hphi, hsucc'⟩)
      · exact absurd h0 (by omega)
      · obtain ⟨_, _, t', hS', hnf', hJ', he'⟩ := hphi
        have hu := IsS_unique hS' hS
        have ht : t' = t := by omega
        rw [ht] at hnf' he'
        have hJm : J' = m := by omega
        rw [hJm] at hsucc'
        obtain ⟨w'', heq, hst'', hiff⟩ := hok hnf'
        have hww : w'' = w' := by omega
        rw [hww] at hiff
        exact hiff.2 hsucc'

/-- Theorem `thm:forest` (4): the states with `J + 1 + w = 2^h` are the initial states
`(K - 1, 2^h - K)` with `2^{h-1} < K ≤ 2^h`. -/
theorem initial_fwd {J w h : ℕ} (hst : IsState J w) (hsum : J + 1 + w = 2 ^ h) :
    J + 1 ≤ 2 ^ h ∧ 2 ^ h < 2 * (J + 1) ∧ w = 2 ^ h - (J + 1) := by
  obtain ⟨_, hw⟩ := hst
  refine ⟨by omega, by omega, by omega⟩

theorem initial_bwd {K h : ℕ} (hK : 2 ≤ K) (h1 : K ≤ 2 ^ h) (h2 : 2 ^ h < 2 * K) :
    IsState (K - 1) (2 ^ h - K) ∧ (K - 1) + 1 + (2 ^ h - K) = 2 ^ h := by
  have hh : h ≠ 0 := by
    rintro rfl
    rw [pow_zero] at h1
    omega
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  have e : 2 ^ (h' + 1) = 2 * 2 ^ h' := by ring
  refine ⟨⟨by omega, by omega⟩, by omega⟩

end SequenceNicolas.States
