module

public import Mathlib
public import SequenceNicolas.Core
public import SequenceNicolas.Recursion
public import SequenceNicolas.States

@[expose] public section

/-!
# The counting identities for `N(J)` and `F(J)`

This module formalizes Proposition `prop:Ncount` (1), the equality `N(2k+1) = N(2k)` of
Proposition `prop:Npairs`, Theorem `thm:forest` (1) (the failing states and their number `F(J)`),
Theorem `thm:forest` (2) (the number of children of a state) and the two counting identities of
Theorem `thm:forest` (3).
-/

namespace SequenceNicolas.Forest

open SequenceNicolas.Recursion SequenceNicolas.States

open scoped Classical

/-! ### The sets `S_J`, the numbers `N(J)` and `F(J)` -/

/-- `S_J`: the integers `0 ≤ w ≤ J - 1` such that the state `(J, w)` is successful. -/
noncomputable def SJ (J : ℕ) : Finset ℕ := (Finset.range J).filter (fun w => Succ J w)

/-- `N(J) = |S_J|`. -/
noncomputable def NJ (J : ℕ) : ℕ := (SJ J).card

/-- The failing states `(J, w)` with `w ≥ 1` of level `J`. -/
noncomputable def FSet (J : ℕ) : Finset ℕ :=
  (Finset.range J).filter (fun w => 1 ≤ w ∧ Fails J w)

/-- `F(J)`: the number of failing states of level `J`. -/
noncomputable def FJ (J : ℕ) : ℕ := (FSet J).card

theorem mem_SJ {J w : ℕ} : w ∈ SJ J ↔ w + 1 ≤ J ∧ Succ J w := by
  unfold SJ
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩

/-- Lemma `lem:sum` consequence: a successful state satisfies `w ≤ J - 1`. -/
theorem succ_bound {J w : ℕ} (hJ : 1 ≤ J) (h : Succ J w) : w + 1 ≤ J := by
  obtain ⟨T, hT, hs⟩ := h
  have h1 : ∑ j ∈ T, j * 2 ^ j ≤ ∑ j ∈ Finset.Icc 1 J, j * 2 ^ j :=
    Finset.sum_le_sum_of_subset hT
  have h2 := SequenceNicolas.Core.sum_j_two_pow J
  have hX : 4 ≤ 2 ^ (J + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (J + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcomm : J * 2 ^ (J + 1) = 2 ^ (J + 1) * J := Nat.mul_comm _ _
  by_contra hc
  have hc' : J ≤ w := by omega
  have hmul : 2 ^ (J + 1) * J ≤ 2 ^ (J + 1) * w := Nat.mul_le_mul_left _ hc'
  omega

/-! ### Proposition `prop:Ncount` (1) -/

/-- Proposition `prop:Ncount` (1): `N(J)` is the number of `T ⊆ {1, …, J}` with
`2^{J+1} ∣ ∑_{j ∈ T} j 2^j`. -/
theorem Ncount {J : ℕ} (hJ : 1 ≤ J) :
    NJ J = ((Finset.Icc 1 J).powerset.filter
      (fun T => 2 ^ (J + 1) ∣ ∑ j ∈ T, j * 2 ^ j)).card := by
  have hpos : 0 < 2 ^ (J + 1) := by positivity
  unfold NJ
  symm
  apply Finset.card_bij (fun T _ => (∑ j ∈ T, j * 2 ^ j) / 2 ^ (J + 1))
  · intro T hT
    rw [Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hsub, q, hq⟩ := hT
    have hdiv : (∑ j ∈ T, j * 2 ^ j) / 2 ^ (J + 1) = q := by
      rw [hq, Nat.mul_div_cancel_left q hpos]
    show (∑ j ∈ T, j * 2 ^ j) / 2 ^ (J + 1) ∈ SJ J
    rw [hdiv]
    have hsucc : Succ J q := ⟨T, hsub, by rw [hq]⟩
    exact mem_SJ.2 ⟨succ_bound hJ hsucc, hsucc⟩
  · intro T1 hT1 T2 hT2 heq
    rw [Finset.mem_filter, Finset.mem_powerset] at hT1 hT2
    obtain ⟨hs1, q1, hq1⟩ := hT1
    obtain ⟨hs2, q2, hq2⟩ := hT2
    have heq' : (∑ j ∈ T1, j * 2 ^ j) / 2 ^ (J + 1) = (∑ j ∈ T2, j * 2 ^ j) / 2 ^ (J + 1) := heq
    rw [hq1, hq2, Nat.mul_div_cancel_left q1 hpos, Nat.mul_div_cancel_left q2 hpos] at heq'
    apply repr_unique J T1 T2 hs1 hs2
    rw [hq1, hq2, heq']
  · intro w hw
    obtain ⟨_, T, hT, hs⟩ := mem_SJ.1 hw
    refine ⟨T, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hT, ⟨w, hs⟩⟩
    · show (∑ j ∈ T, j * 2 ^ j) / 2 ^ (J + 1) = w
      rw [hs, Nat.mul_div_cancel_left w hpos]

/-! ### Proposition `prop:Npairs`: `N(2k+1) = N(2k)` -/

/-- The map `c ↦ (c + x (m+1)) / 2` of Theorem `thm:bottomup` (1), with `x ≡ c (mod 2)`. -/
def pf (m c : ℕ) : ℕ := (c + (c % 2) * (m + 1)) / 2

theorem pf_spec {m : ℕ} (hm : m % 2 = 0) (c : ℕ) : c + (c % 2) * (m + 1) = 2 * pf m c := by
  unfold pf
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · rw [h]
    omega
  · rw [h]
    omega

/-- Proposition `prop:Npairs`: `N(2k+1) = N(2k)` for `k ≥ 1`. -/
theorem N_odd_eq {k : ℕ} (hk : 1 ≤ k) : NJ (2 * k + 1) = NJ (2 * k) := by
  have hm : (2 * k) % 2 = 0 := by omega
  unfold NJ
  symm
  apply Finset.card_bij (fun c _ => pf (2 * k) c)
  · intro c hc
    obtain ⟨hcm, hsc⟩ := mem_SJ.1 hc
    have hsp := pf_spec hm c
    have hx : c % 2 ≤ 1 := by omega
    refine mem_SJ.2 ⟨?_, ?_⟩
    · rcases Nat.mod_two_eq_zero_or_one c with h | h
      · rw [h] at hsp
        omega
      · rw [h] at hsp
        omega
    · exact bottomup_iff.2 ⟨c, c % 2, hsc, hx, hsp⟩
  · intro c1 hc1 c2 hc2 heq
    obtain ⟨hb1, _⟩ := mem_SJ.1 hc1
    obtain ⟨hb2, _⟩ := mem_SJ.1 hc2
    have heq' : pf (2 * k) c1 = pf (2 * k) c2 := heq
    have s1 := pf_spec hm c1
    have s2 := pf_spec hm c2
    rcases Nat.mod_two_eq_zero_or_one c1 with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one c2 with h2 | h2 <;>
      rw [h1] at s1 <;> rw [h2] at s2 <;> omega
  · intro w hw
    obtain ⟨_, hsw⟩ := mem_SJ.1 hw
    obtain ⟨c, x, hsc, hx, hcx⟩ := bottomup_iff.1 hsw
    have hcb : c + 1 ≤ 2 * k := succ_bound (by omega) hsc
    have hcm : c ∈ SJ (2 * k) := mem_SJ.2 ⟨hcb, hsc⟩
    refine ⟨c, hcm, ?_⟩
    show pf (2 * k) c = w
    have s1 := pf_spec hm c
    rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
      rcases Nat.mod_two_eq_zero_or_one c with h1 | h1 <;>
      rw [h1] at s1 <;> omega

/-! ### Theorem `thm:forest` (1): failing states -/

/-- For fixed `J` and `w ≥ 1`, the integer `t` with `2^t w + t + 1 = J + 1` is unique
(the quotient `(J+1-σ)/2^{σ-1}` is strictly decreasing in `σ = t + 1`). -/
theorem fails_unique_t {J w t t' : ℕ} (hw : 1 ≤ w) (h : 2 ^ t * w + (t + 1) = J + 1)
    (h' : 2 ^ t' * w + (t' + 1) = J + 1) : t = t' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have h1 := f_step (w := w) (t := t) hw
    have h2 := f_mono (w := w) (σ := t + 1) (t := t') (by omega)
    omega
  · have h1 := f_step (w := w) (t := t') hw
    have h2 := f_mono (w := w) (σ := t' + 1) (t := t) (by omega)
    omega

/-- Theorem `thm:forest` (1): `F(J)` is the number of integers `σ = t + 1 ≥ 2` with
`2^{σ-1} ∣ J + 1 - σ` and `J + 1 - σ ≥ 2^{σ-1}`; the failing state is
`w = (J + 1 - σ) / 2^{σ-1}`. -/
theorem F_count {J : ℕ} :
    FJ J = ((Finset.range J).filter
      (fun t => 1 ≤ t ∧ 2 ^ t ∣ J - t ∧ 2 ^ t ≤ J - t)).card := by
  unfold FJ
  symm
  apply Finset.card_bij (fun t _ => (J - t) / 2 ^ t)
  · intro t ht
    rw [Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨htJ, ht1, ⟨q, hq⟩, hle⟩ := ht
    have hpos : 0 < 2 ^ t := by positivity
    have hdiv : (J - t) / 2 ^ t = q := by
      rw [hq, Nat.mul_div_cancel_left q hpos]
    show (J - t) / 2 ^ t ∈ FSet J
    rw [hdiv]
    have h2 : 2 ≤ 2 ^ t := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht1
    have hq1 : 1 ≤ q := by
      by_contra hc
      have : q = 0 := by omega
      rw [this] at hq
      omega
    have hq2 : 2 * q ≤ 2 ^ t * q := Nat.mul_le_mul_right q h2
    have hst : IsState J q := ⟨by omega, by omega⟩
    simp only [FSet, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, hq1, ?_⟩
    exact (fails_iff hst hq1).2 ⟨t, ht1, by omega⟩
  · intro t1 ht1 t2 ht2 heq
    rw [Finset.mem_filter, Finset.mem_range] at ht1 ht2
    obtain ⟨_, a1, ⟨q1, hq1⟩, b1⟩ := ht1
    obtain ⟨_, a2, ⟨q2, hq2⟩, b2⟩ := ht2
    have hp1 : 0 < 2 ^ t1 := by positivity
    have hp2 : 0 < 2 ^ t2 := by positivity
    have heq' : (J - t1) / 2 ^ t1 = (J - t2) / 2 ^ t2 := heq
    rw [hq1, Nat.mul_div_cancel_left q1 hp1] at heq'
    rw [hq2, Nat.mul_div_cancel_left q2 hp2] at heq'
    rw [← heq'] at hq2
    have hq1pos : 1 ≤ q1 := by
      by_contra hc
      have : q1 = 0 := by omega
      rw [this] at hq1
      omega
    exact fails_unique_t (J := J) (w := q1) hq1pos (by omega) (by omega)
  · intro w hw
    simp only [FSet, Finset.mem_filter, Finset.mem_range] at hw
    obtain ⟨hwJ, hw1, hfail⟩ := hw
    have hst : IsState J w := ⟨by omega, by omega⟩
    obtain ⟨t, ht1, he⟩ := (fails_iff hst hw1).1 hfail
    have hpos : 0 < 2 ^ t := by positivity
    have h1w : 2 ^ t * 1 ≤ 2 ^ t * w := Nat.mul_le_mul_left _ hw1
    have hJt : J - t = 2 ^ t * w := by omega
    refine ⟨t, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ht1, ⟨w, hJt⟩, by omega⟩
    · show (J - t) / 2 ^ t = w
      rw [hJt, Nat.mul_div_cancel_left w hpos]

/-! ### Theorem `thm:forest` (2): the children of a state -/

/-- The preimages of `(J', w')` under `Φ`: `(J, w)` with `J = J' + σ`, `w = u / 2^σ`,
`2^σ ∣ u = J' + 1 + w'`, `σ = t + 1 ≥ 1`. -/
theorem children_eq {J w J' w' : ℕ} (hst' : IsState J' w') :
    Phi J w J' w' ↔ ∃ t, 2 ^ (t + 1) ∣ J' + 1 + w' ∧ J = J' + (t + 1) ∧
      w = (J' + 1 + w') / 2 ^ (t + 1) := by
  rw [phi_iff hst']
  constructor
  · rintro ⟨t, hJ, he⟩
    have hpos : 0 < 2 ^ (t + 1) := by positivity
    refine ⟨t, ⟨w, he.symm⟩, hJ, ?_⟩
    rw [← he, Nat.mul_div_cancel_left w hpos]
  · rintro ⟨t, ⟨q, hq⟩, hJ, hw⟩
    have hpos : 0 < 2 ^ (t + 1) := by positivity
    have hwq : w = q := by
      rw [hw, hq, Nat.mul_div_cancel_left q hpos]
    refine ⟨t, hJ, ?_⟩
    rw [hwq]
    exact hq.symm

/-- Theorem `thm:forest` (2): the number of children of `(J', w')` is `v_2(J' + 1 + w')`. -/
theorem children_card {J' w' : ℕ} (_hst' : IsState J' w') :
    ((Finset.range (J' + 1 + w')).filter (fun t => 2 ^ (t + 1) ∣ J' + 1 + w')).card
      = padicValNat 2 (J' + 1 + w') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu : J' + 1 + w' ≠ 0 := by omega
  have : (Finset.range (J' + 1 + w')).filter (fun t => 2 ^ (t + 1) ∣ J' + 1 + w')
      = Finset.range (padicValNat 2 (J' + 1 + w')) := by
    ext t
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range]
    constructor
    · rintro ⟨_, hd⟩
      have := (padicValNat_dvd_iff_le hu).1 hd
      omega
    · intro ht
      have hd : 2 ^ (t + 1) ∣ J' + 1 + w' := (padicValNat_dvd_iff_le hu).2 (by omega)
      have hle : 2 ^ (t + 1) ≤ J' + 1 + w' := Nat.le_of_dvd (by omega) hd
      have h1 := nat_lt_two_pow t
      have h2 : 2 ^ t ≤ 2 ^ (t + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact ⟨by omega, hd⟩
  rw [this, Finset.card_range]

/-! ### Theorem `thm:forest` (3): the counting identities -/

/-- `Φ` takes values in states. -/
theorem phi_state {J w J' w' : ℕ} (h : Phi J w J' w') : IsState J' w' := by
  obtain ⟨hst, hw, t, hS, hnf, hJ, he⟩ := h
  obtain ⟨s, hS2, hs⟩ := exists_S hst hw
  have hu := IsS_unique hS hS2
  subst hJ
  have hm1 : 1 ≤ J' := by omega
  obtain ⟨w'', heq, hst'', _⟩ := (step_main hst hw hS hm1).2 hnf
  have hww : w'' = w' := by omega
  rw [hww] at hst''
  exact hst''

/-- Every state with `w ≥ 1` either fails or has an image under `Φ`, and not both. -/
theorem fails_or_phi {J w : ℕ} (hst : IsState J w) (hw : 1 ≤ w) :
    (Fails J w ∧ ¬ ∃ J' w', Phi J w J' w') ∨ (¬ Fails J w ∧ ∃ J' w', Phi J w J' w') := by
  obtain ⟨s, hS, hsJ⟩ := exists_S hst hw
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by have := hS.1; omega⟩
  by_cases hf : 2 ^ t * w + (t + 1) = J + 1
  · left
    refine ⟨⟨t, hS, hf⟩, ?_⟩
    rintro ⟨J', w', _, _, t', hS', hne, _, _⟩
    have := IsS_unique hS' hS
    have ht : t' = t := by omega
    rw [ht] at hne
    exact hne hf
  · right
    refine ⟨?_, ?_⟩
    · rintro ⟨t', hS', hf'⟩
      have := IsS_unique hS' hS
      have ht : t' = t := by omega
      rw [ht] at hf'
      exact hf hf'
    · have h2 := hS.2.1
      refine ⟨J - (t + 1), 2 ^ (t + 1) * w + (t + 1) - J - 1, hst, hw, t, hS, hf, ?_, ?_⟩
      · omega
      · omega

/-- A failing state is not successful. -/
theorem not_succ_of_fails {J w : ℕ} (hst : IsState J w) (hw : 1 ≤ w) (h : Fails J w) :
    ¬ Succ J w := by
  obtain ⟨t, hS, hf⟩ := h
  obtain ⟨s, hS2, hs⟩ := exists_S hst hw
  have hu := IsS_unique hS hS2
  obtain ⟨m, hm⟩ : ∃ m, J = m + (t + 1) := ⟨J - (t + 1), by omega⟩
  have hm1 : 1 ≤ m := by omega
  subst hm
  exact (step_main hst hw hS hm1).1 hf

/-- Counting the states of level `J` with `w ≥ 1` that do not fail, grouped by `σ = t + 1`
(Theorem `thm:forest` (2) and (3)). -/
theorem count_children (J : ℕ) (Q : ℕ → ℕ → Prop) :
    ((Finset.range J).filter (fun w => 1 ≤ w ∧ ∃ J' w', Phi J w J' w' ∧ Q J' w')).card
      = ∑ σ ∈ Finset.Icc 1 (J - 1),
          ((Finset.range (J - σ)).filter
            (fun w' => Q (J - σ) w' ∧ 2 ^ σ ∣ J - σ + 1 + w')).card := by
  have hσ : ((Finset.Icc 1 (J - 1)).sigma (fun σ => (Finset.range (J - σ)).filter
      (fun w' => Q (J - σ) w' ∧ 2 ^ σ ∣ J - σ + 1 + w'))).card
      = ∑ σ ∈ Finset.Icc 1 (J - 1), ((Finset.range (J - σ)).filter
          (fun w' => Q (J - σ) w' ∧ 2 ^ σ ∣ J - σ + 1 + w')).card :=
    Finset.card_sigma _ _
  rw [← hσ]
  symm
  apply Finset.card_bij (fun (p : Σ _ : ℕ, ℕ) _ => (J - p.1 + 1 + p.2) / 2 ^ p.1)
  · rintro ⟨σ, w'⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨⟨hσ1, hσ2⟩, hw'J, hQ, ⟨q, hq⟩⟩ := hp
    have hpos : 0 < 2 ^ σ := by positivity
    have hdiv : (J - σ + 1 + w') / 2 ^ σ = q := by
      rw [hq, Nat.mul_div_cancel_left q hpos]
    show (J - σ + 1 + w') / 2 ^ σ ∈ _
    rw [hdiv]
    have h2 : 2 ≤ 2 ^ σ := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ σ := Nat.pow_le_pow_right (by norm_num) hσ1
    have hq1 : 1 ≤ q := by
      by_contra hc
      have : q = 0 := by omega
      rw [this] at hq
      omega
    have hq2 : 2 * q ≤ 2 ^ σ * q := Nat.mul_le_mul_right q h2
    have hst' : IsState (J - σ) w' := ⟨by omega, by omega⟩
    have hphi : Phi J q (J - σ) w' := by
      rw [children_eq hst']
      refine ⟨σ - 1, ?_, by omega, ?_⟩
      · have : σ - 1 + 1 = σ := by omega
        rw [this]
        exact ⟨q, hq⟩
      · have : σ - 1 + 1 = σ := by omega
        rw [this, hq, Nat.mul_div_cancel_left q hpos]
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hq1, J - σ, w', hphi, hQ⟩
  · rintro ⟨σ1, w1⟩ hp1 ⟨σ2, w2⟩ hp2 heq
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range] at hp1 hp2
    obtain ⟨⟨a1, a2⟩, b1, c1, ⟨q1, hq1⟩⟩ := hp1
    obtain ⟨⟨a1', a2'⟩, b1', c1', ⟨q2, hq2⟩⟩ := hp2
    have hpos1 : 0 < 2 ^ σ1 := by positivity
    have hpos2 : 0 < 2 ^ σ2 := by positivity
    have heq' : (J - σ1 + 1 + w1) / 2 ^ σ1 = (J - σ2 + 1 + w2) / 2 ^ σ2 := heq
    have hd1 : (J - σ1 + 1 + w1) / 2 ^ σ1 = q1 := by
      rw [hq1, Nat.mul_div_cancel_left q1 hpos1]
    have hd2 : (J - σ2 + 1 + w2) / 2 ^ σ2 = q2 := by
      rw [hq2, Nat.mul_div_cancel_left q2 hpos2]
    rw [hd1, hd2] at heq'
    rw [← heq'] at hq2
    have hst1 : IsState (J - σ1) w1 := ⟨by omega, by omega⟩
    have hst2 : IsState (J - σ2) w2 := ⟨by omega, by omega⟩
    have hph1 : Phi J q1 (J - σ1) w1 := by
      rw [children_eq hst1]
      refine ⟨σ1 - 1, ?_, by omega, ?_⟩
      · have : σ1 - 1 + 1 = σ1 := by omega
        rw [this]
        exact ⟨q1, hq1⟩
      · have : σ1 - 1 + 1 = σ1 := by omega
        rw [this, hq1, Nat.mul_div_cancel_left q1 hpos1]
    have hph2 : Phi J q1 (J - σ2) w2 := by
      rw [children_eq hst2]
      refine ⟨σ2 - 1, ?_, by omega, ?_⟩
      · have : σ2 - 1 + 1 = σ2 := by omega
        rw [this]
        exact ⟨q1, hq2⟩
      · have : σ2 - 1 + 1 = σ2 := by omega
        rw [this, hq2, Nat.mul_div_cancel_left q1 hpos2]
    obtain ⟨hJe, hwe⟩ := phi_unique hph1 hph2
    have hσ : σ1 = σ2 := by omega
    subst hσ
    subst hwe
    rfl
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_range] at hw
    obtain ⟨hwJ, hw1, J', w', hphi, hQ⟩ := hw
    have hst' := phi_state hphi
    obtain ⟨hst, _, t, hS, hne, hJ, he⟩ := hphi
    have hphi' : Phi J w J' w' := ⟨hst, hw1, t, hS, hne, hJ, he⟩
    obtain ⟨hJ1, hw'J⟩ := hst'
    have hpos : 0 < 2 ^ (t + 1) := by positivity
    have hu : 2 ^ (t + 1) * w = J' + 1 + w' := by omega
    refine ⟨⟨t + 1, w'⟩, ?_, ?_⟩
    · have hJσ : J - (t + 1) = J' := by omega
      simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range, hJσ]
      exact ⟨⟨by omega, by omega⟩, by omega, hQ, ⟨w, by omega⟩⟩
    · show (J - (t + 1) + 1 + w') / 2 ^ (t + 1) = w
      have hJσ : J - (t + 1) = J' := by omega
      rw [hJσ, ← hu, Nat.mul_div_cancel_left w hpos]

/-- Theorem `thm:forest` (3): `N(J) = 1 + ∑_{σ=1}^{J-1} #{w' ∈ S_{J-σ} : 2^σ ∣ J-σ+1+w'}`. -/
theorem N_identity {J : ℕ} (hJ : 1 ≤ J) :
    NJ J = 1 + ∑ σ ∈ Finset.Icc 1 (J - 1),
      ((SJ (J - σ)).filter (fun w' => 2 ^ σ ∣ J - σ + 1 + w')).card := by
  have hcount := count_children J (fun J' w' => Succ J' w')
  have hset : SJ J = insert 0 ((Finset.range J).filter
      (fun w => 1 ≤ w ∧ ∃ J' w', Phi J w J' w' ∧ Succ J' w')) := by
    ext w
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range, mem_SJ]
    constructor
    · rintro ⟨hw, hs⟩
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · exact Or.inl h0
      · right
        have hst : IsState J w := ⟨hJ, hw⟩
        rcases (succ_iff_phi hst).1 hs with h | h
        · omega
        · exact ⟨by omega, h0, h⟩
    · rintro (h0 | ⟨hw, h1, J', w', hphi, hs'⟩)
      · subst h0
        exact ⟨by omega, succ_zero J⟩
      · refine ⟨by omega, ?_⟩
        have hst : IsState J w := ⟨hJ, by omega⟩
        exact (succ_iff_phi hst).2 (Or.inr ⟨J', w', hphi, hs'⟩)
  have hnot : 0 ∉ (Finset.range J).filter
      (fun w => 1 ≤ w ∧ ∃ J' w', Phi J w J' w' ∧ Succ J' w') := by
    rw [Finset.mem_filter]
    rintro ⟨_, h, _⟩
    omega
  unfold NJ
  rw [hset]
  rw [Finset.card_insert_of_notMem hnot]
  rw [hcount, Nat.add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Finset.mem_Icc] at hσ
  congr 1
  ext w'
  simp only [Finset.mem_filter, Finset.mem_range, mem_SJ]
  constructor
  · rintro ⟨hw, hs, hd⟩
    exact ⟨⟨by omega, hs⟩, hd⟩
  · rintro ⟨⟨hw, hs⟩, hd⟩
    exact ⟨by omega, hs, hd⟩

/-- Theorem `thm:forest` (3): `J = 1 + F(J) + ∑_{σ=1}^{J-1} #{0 ≤ w' ≤ J-σ-1 : 2^σ ∣ J-σ+1+w'}`. -/
theorem J_identity {J : ℕ} (hJ : 1 ≤ J) :
    J = 1 + FJ J + ∑ σ ∈ Finset.Icc 1 (J - 1),
      ((Finset.range (J - σ)).filter (fun w' => 2 ^ σ ∣ J - σ + 1 + w')).card := by
  have hcount : ((Finset.range J).filter
      (fun w => 1 ≤ w ∧ ∃ J' w', Phi J w J' w' ∧ True)).card
      = ∑ σ ∈ Finset.Icc 1 (J - 1),
          ((Finset.range (J - σ)).filter
            (fun w' => True ∧ 2 ^ σ ∣ J - σ + 1 + w')).card :=
    by convert count_children J (fun _ _ => True)
  have hP : ((Finset.range J).filter
      (fun w => 1 ≤ w ∧ ∃ J' w', Phi J w J' w' ∧ True)).card
      = ∑ σ ∈ Finset.Icc 1 (J - 1),
        ((Finset.range (J - σ)).filter (fun w' => 2 ^ σ ∣ J - σ + 1 + w')).card := by
    rw [hcount]
    apply Finset.sum_congr rfl
    intro σ _
    refine congrArg Finset.card ?_
    ext w'
    simp
  rw [← hP]
  have hset : Finset.range J = insert 0 (FSet J ∪ (Finset.range J).filter
      (fun w => 1 ≤ w ∧ ∃ J' w', Phi J w J' w' ∧ True)) := by
    ext w
    simp only [Finset.mem_insert, Finset.mem_union, FSet, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hw
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · exact Or.inl h0
      · right
        have hst : IsState J w := ⟨hJ, hw⟩
        rcases fails_or_phi hst h0 with ⟨hf, _⟩ | ⟨_, J', w', hphi⟩
        · exact Or.inl ⟨hw, h0, hf⟩
        · exact Or.inr ⟨hw, h0, J', w', hphi, trivial⟩
    · rintro (h0 | ⟨hw, _⟩ | ⟨hw, _⟩)
      · omega
      · exact hw
      · exact hw
  have hnot : 0 ∉ FSet J ∪ (Finset.range J).filter
      (fun w => 1 ≤ w ∧ ∃ J' w', Phi J w J' w' ∧ True) := by
    simp only [Finset.mem_union, FSet, Finset.mem_filter, Finset.mem_range]
    rintro (⟨_, h, _⟩ | ⟨_, h, _⟩) <;> omega
  have hdisj : Disjoint (FSet J) ((Finset.range J).filter
      (fun w => 1 ≤ w ∧ ∃ J' w', Phi J w J' w' ∧ True)) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    simp only [FSet, Finset.mem_filter, Finset.mem_range] at hw1
    simp only [Finset.mem_filter, Finset.mem_range] at hw2
    obtain ⟨hwJ, h1, hf⟩ := hw1
    obtain ⟨_, _, J', w', hphi, _⟩ := hw2
    have hst : IsState J w := ⟨hJ, by omega⟩
    rcases fails_or_phi hst h1 with ⟨_, hn⟩ | ⟨hn, _⟩
    · exact hn ⟨J', w', hphi⟩
    · exact hn hf
  have hcard : J = (insert 0 (FSet J ∪ (Finset.range J).filter
      (fun w => 1 ≤ w ∧ ∃ J' w', Phi J w J' w' ∧ True))).card := by
    rw [← hset, Finset.card_range]
  rw [Finset.card_insert_of_notMem hnot] at hcard
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  unfold FJ
  omega

end SequenceNicolas.Forest
