module

public import Mathlib
public import SequenceNicolas.Core
public import SequenceNicolas.Recursion
public import SequenceNicolas.States
public import SequenceNicolas.Forest

@[expose] public section

/-!
# Divisibility of `N(J)` by 4, the sum of `F(J)`, and the roots of the forest

This module formalizes the second half of Proposition `prop:Npairs` (`4 ∣ N(J)` for `J ≥ 4`), the
formula for `∑_{J ≤ L} F(J)` of Theorem `thm:forest` (1) and Proposition `prop:roots`.
-/

namespace SequenceNicolas.Roots

open SequenceNicolas.Recursion SequenceNicolas.States SequenceNicolas.Forest

open scoped Classical

theorem card_split (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p]
    [DecidablePred (fun a => ¬ p a)] :
    (s.filter p).card + (s.filter (fun a => ¬ p a)).card = s.card := by
  first
  | exact Finset.filter_card_add_filter_neg_card_eq_card p
  | exact Finset.card_filter_add_card_filter_not p

/-! ### The complement set of the symmetry (Proposition `prop:symmetry`) -/

/-- If `T ⊆ {1, …, J}` represents `2^{J+1} w`, then `1 ∉ T` and the set
`{1, …, J} \ ({1} ∪ T)` represents `2^{J+1} (J - 1 - w)`. -/
theorem symm_set {J w : ℕ} {T : Finset ℕ} (hJ : 2 ≤ J) (hw : w + 1 ≤ J)
    (hT : T ⊆ Finset.Icc 1 J) (hs : ∑ j ∈ T, j * 2 ^ j = 2 ^ (J + 1) * w) :
    1 ∉ T ∧ ∑ j ∈ Finset.Icc 1 J \ insert 1 T, j * 2 ^ j = 2 ^ (J + 1) * (J - 1 - w) := by
  have hX8 : 8 ∣ 2 ^ (J + 1) := by
    have h3 : 2 ^ 3 ∣ 2 ^ (J + 1) := pow_dvd_pow 2 (by omega)
    exact h3
  have h8 : 8 ∣ ∑ j ∈ T, j * 2 ^ j := by
    rw [hs]
    exact Dvd.dvd.mul_right hX8 w
  have h1 := no_one hT h8
  refine ⟨h1, ?_⟩
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
  have h2 := SequenceNicolas.Core.sum_j_two_pow J
  obtain ⟨d, hd⟩ : ∃ d, J = w + d + 1 := ⟨J - 1 - w, by omega⟩
  have e : J - 1 - w = d := by omega
  have hJX : J * 2 ^ (J + 1) = w * 2 ^ (J + 1) + d * 2 ^ (J + 1) + 2 ^ (J + 1) := by
    have : J * 2 ^ (J + 1) = (w + d + 1) * 2 ^ (J + 1) := by rw [← hd]
    rw [this]
    ring
  rw [e]
  have hc2 : 2 ^ (J + 1) * w = w * 2 ^ (J + 1) := Nat.mul_comm _ _
  have hc3 : 2 ^ (J + 1) * d = d * 2 ^ (J + 1) := Nat.mul_comm _ _
  nlinarith [hsd, hUsum, h2, hs, hJX, hc2, hc3]

/-- The symmetry `w ↦ J - 1 - w` has no fixed point on successful states of level `J ≥ 2`. -/
theorem no_fixed {m c : ℕ} (hm : 2 ≤ m) (h : Succ m c) (hc : 2 * c + 1 = m) : False := by
  obtain ⟨T, hT, hs⟩ := h
  have hw : c + 1 ≤ m := by omega
  obtain ⟨h1, hsum⟩ := symm_set hm hw hT hs
  have e : m - 1 - c = c := by omega
  rw [e] at hsum
  have hT' : Finset.Icc 1 m \ insert 1 T ⊆ Finset.Icc 1 m := fun x hx => (Finset.mem_sdiff.1 hx).1
  have hEq : T = Finset.Icc 1 m \ insert 1 T := repr_unique m T _ hT hT' (hs.trans hsum.symm)
  have hempty : T = ∅ := by
    by_contra hne
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have hx' : x ∈ Finset.Icc 1 m \ insert 1 T := by rw [← hEq]; exact hx
    exact (Finset.mem_sdiff.1 hx').2 (Finset.mem_insert_of_mem hx)
  rw [hempty, Finset.sum_empty] at hs
  have hpos : 0 < 2 ^ (m + 1) := by positivity
  have hc0 : c = 0 := by
    rcases Nat.mul_eq_zero.1 hs.symm with h0 | h0
    · omega
    · exact h0
  omega

/-! ### Proposition `prop:Npairs`: `4 ∣ N(J)` -/

theorem four_dvd_even {k : ℕ} (hk : 2 ≤ k) : 4 ∣ NJ (2 * k) := by
  obtain ⟨m, hm⟩ : ∃ m, 2 * k = m + 1 := ⟨2 * k - 1, by omega⟩
  have hm2 : 3 ≤ m := by omega
  rw [hm]
  -- the even members of `S_m`
  let E : Finset ℕ := (SJ m).filter (fun c => c % 2 = 0)
  have hN : NJ (m + 1) = 2 * E.card := by
    unfold NJ
    have hprod : (E ×ˢ Finset.range 2).card = E.card * 2 := by
      rw [Finset.card_product, Finset.card_range]
    rw [Nat.mul_comm, ← hprod]
    symm
    apply Finset.card_bij (fun (p : ℕ × ℕ) _ => (p.1 + p.2 * (m + 1)) / 2)
    · rintro ⟨c, x⟩ hp
      simp only [E, Finset.mem_product, Finset.mem_filter, Finset.mem_range, mem_SJ] at hp
      obtain ⟨⟨⟨hcm, hsc⟩, hc2⟩, hx⟩ := hp
      show (c + x * (m + 1)) / 2 ∈ SJ (m + 1)
      rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl
      · refine mem_SJ.2 ⟨by omega, ?_⟩
        exact bottomup_iff.2 ⟨c, 0, hsc, by omega, by omega⟩
      · refine mem_SJ.2 ⟨by omega, ?_⟩
        exact bottomup_iff.2 ⟨c, 1, hsc, by omega, by omega⟩
    · rintro ⟨c1, x1⟩ hp1 ⟨c2, x2⟩ hp2 heq
      simp only [E, Finset.mem_product, Finset.mem_filter, Finset.mem_range, mem_SJ] at hp1 hp2
      obtain ⟨⟨⟨hcm1, _⟩, hc21⟩, hx1⟩ := hp1
      obtain ⟨⟨⟨hcm2, _⟩, hc22⟩, hx2⟩ := hp2
      have heq' : (c1 + x1 * (m + 1)) / 2 = (c2 + x2 * (m + 1)) / 2 := heq
      rcases (by omega : x1 = 0 ∨ x1 = 1) with rfl | rfl <;>
        rcases (by omega : x2 = 0 ∨ x2 = 1) with rfl | rfl <;>
        first
        | (exfalso; omega)
        | (have hc : c1 = c2 := by omega
           rw [hc])
    · intro w hw
      obtain ⟨_, hsw⟩ := mem_SJ.1 hw
      obtain ⟨c, x, hsc, hx, hcx⟩ := bottomup_iff.1 hsw
      have hcb : c + 1 ≤ m := succ_bound (by omega) hsc
      refine ⟨(c, x), ?_, ?_⟩
      · simp only [E, Finset.mem_product, Finset.mem_filter, Finset.mem_range, mem_SJ]
        rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl
        · exact ⟨⟨⟨hcb, hsc⟩, by omega⟩, by omega⟩
        · exact ⟨⟨⟨hcb, hsc⟩, by omega⟩, by omega⟩
      · show (c + x * (m + 1)) / 2 = w
        omega
  -- the involution `c ↦ m - 1 - c` on `E` has no fixed point
  have hnf : ∀ c ∈ E, 2 * c + 1 ≠ m := by
    intro c hc h
    simp only [E, Finset.mem_filter, mem_SJ] at hc
    exact no_fixed (by omega) hc.1.2 h
  have hsplit : (E.filter (fun c => 2 * c + 1 < m)).card
      + (E.filter (fun c => ¬ (2 * c + 1 < m))).card = E.card :=
    card_split E (fun c => 2 * c + 1 < m)
  have hhigh : (E.filter (fun c => ¬ (2 * c + 1 < m))).card
      = (E.filter (fun c => m < 2 * c + 1)).card := by
    congr 1
    apply Finset.filter_congr
    intro c hc
    have := hnf c hc
    omega
  have hcard : (E.filter (fun c => m < 2 * c + 1)).card = (E.filter (fun c => 2 * c + 1 < m)).card := by
    symm
    apply Finset.card_bij (fun c _ => m - 1 - c)
    · intro c hc
      simp only [E, Finset.mem_filter, mem_SJ] at hc ⊢
      obtain ⟨⟨⟨hcm, hsc⟩, hc2⟩, hlow⟩ := hc
      have hsym := (succ_symm (by omega : 1 ≤ m) hcm).1 hsc
      exact ⟨⟨⟨by omega, hsym⟩, by omega⟩, by omega⟩
    · intro c1 hc1 c2 hc2 heq
      simp only [E, Finset.mem_filter, mem_SJ] at hc1 hc2
      have heq' : m - 1 - c1 = m - 1 - c2 := heq
      omega
    · intro d hd
      simp only [E, Finset.mem_filter, mem_SJ] at hd
      obtain ⟨⟨⟨hdm, hsd⟩, hd2⟩, hhi⟩ := hd
      have hsym := (succ_symm (by omega : 1 ≤ m) hdm).1 hsd
      refine ⟨m - 1 - d, ?_, ?_⟩
      · simp only [E, Finset.mem_filter, mem_SJ]
        exact ⟨⟨⟨by omega, hsym⟩, by omega⟩, by omega⟩
      · show m - 1 - (m - 1 - d) = d
        omega
  rw [hN]
  omega

/-- Proposition `prop:Npairs`: `4 ∣ N(J)` for every `J ≥ 4`. -/
theorem four_dvd {J : ℕ} (hJ : 4 ≤ J) : 4 ∣ NJ J := by
  rcases Nat.even_or_odd' J with ⟨k, hk | hk⟩
  · rw [hk]
    exact four_dvd_even (by omega)
  · rw [hk, N_odd_eq (k := k) (by omega)]
    exact four_dvd_even (by omega)

/-! ### Theorem `thm:forest` (1): the sum of `F(J)` -/

/-- For `1 ≤ t`, the number of `J ∈ [1, L]` with `2^t ∣ J - t` and `2^t ≤ J - t` is `⌊(L-t)/2^t⌋`. -/
theorem count_multiples {L t : ℕ} (ht : 1 ≤ t) :
    ((Finset.Icc 1 L).filter (fun J => 2 ^ t ∣ J - t ∧ 2 ^ t ≤ J - t)).card = (L - t) / 2 ^ t := by
  have hpos : 0 < 2 ^ t := by positivity
  have hlt := nat_lt_two_pow t
  have hcard : (Finset.Icc 1 ((L - t) / 2 ^ t)).card = (L - t) / 2 ^ t := by
    rw [Nat.card_Icc]
    exact Nat.add_sub_cancel _ _
  rw [← hcard]
  symm
  apply Finset.card_bij (fun q _ => t + 2 ^ t * q)
  · intro q hq
    rw [Finset.mem_Icc] at hq
    obtain ⟨hq1, hq2⟩ := hq
    have h1 : 2 ^ t * q ≤ 2 ^ t * ((L - t) / 2 ^ t) := Nat.mul_le_mul_left _ hq2
    have h2 : 2 ^ t * ((L - t) / 2 ^ t) ≤ L - t := Nat.mul_div_le (L - t) (2 ^ t)
    have h3 : 2 ^ t * 1 ≤ 2 ^ t * q := Nat.mul_le_mul_left _ hq1
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ⟨q, by omega⟩, by omega⟩
  · intro q1 hq1 q2 hq2 heq
    have heq' : t + 2 ^ t * q1 = t + 2 ^ t * q2 := heq
    exact Nat.eq_of_mul_eq_mul_left hpos (by omega)
  · intro J hJ
    simp only [Finset.mem_filter, Finset.mem_Icc] at hJ
    obtain ⟨⟨hJ1, hJL⟩, ⟨q, hq⟩, hle⟩ := hJ
    have hq1 : 1 ≤ q := by
      by_contra hc
      have : q = 0 := by omega
      rw [this] at hq
      omega
    have hqle : q ≤ (L - t) / 2 ^ t := by
      rw [Nat.le_div_iff_mul_le hpos]
      have : 2 ^ t * q = q * 2 ^ t := Nat.mul_comm _ _
      omega
    refine ⟨q, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨hq1, hqle⟩
    · show t + 2 ^ t * q = J
      omega

/-- Theorem `thm:forest` (1): `∑_{J=1}^{L} F(J) = ∑_{σ=2}^{L} ⌊(L+1-σ)/2^{σ-1}⌋`, written with
`t = σ - 1`. -/
theorem F_sum (L : ℕ) :
    ∑ J ∈ Finset.Icc 1 L, FJ J = ∑ t ∈ Finset.Icc 1 (L - 1), (L - t) / 2 ^ t := by
  have hF : ∀ J ∈ Finset.Icc 1 L, FJ J =
      ((Finset.Icc 1 (L - 1)).filter (fun t => 2 ^ t ∣ J - t ∧ 2 ^ t ≤ J - t)).card := by
    intro J hJ
    rw [Finset.mem_Icc] at hJ
    rw [F_count]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    have hlt := nat_lt_two_pow t
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h2, by omega⟩, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨by omega, h1, h3, h4⟩
  rw [Finset.sum_congr rfl hF]
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_Icc] at ht
  rw [← Finset.card_filter]
  exact count_multiples ht.1

/-! ### Proposition `prop:roots` -/

/-- `Reach a b`: `b` is obtained from `a` by iterating `Φ` (the orbit of Section `sec:states`). -/
def Reach (a b : ℕ × ℕ) : Prop :=
  Relation.ReflTransGen (fun x y : ℕ × ℕ => Phi x.1 x.2 y.1 y.2) a b

/-- If `Φ(J, w) = (J', w')`, `T'` represents `2^{J'+1} w'` then `T' ∪ {J'+1}` represents
`2^{J+1} w` (the greedy step of Lemma `lem:greedy`). -/
theorem phi_repr {J w J' w' : ℕ} {T : Finset ℕ} (h : Phi J w J' w')
    (hT : T ⊆ Finset.Icc 1 J') (hs : ∑ j ∈ T, j * 2 ^ j = 2 ^ (J' + 1) * w') :
    insert (J' + 1) T ⊆ Finset.Icc 1 J ∧
      ∑ j ∈ insert (J' + 1) T, j * 2 ^ j = 2 ^ (J + 1) * w := by
  obtain ⟨hst, hw, t, hS, hne, hJ, he⟩ := h
  have hu : 2 ^ (t + 1) * w = J' + 1 + w' := by omega
  have hnot : J' + 1 ∉ T := fun hm => by
    have := (Finset.mem_Icc.1 (hT hm)).2
    omega
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx'
    · exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    · have := Finset.mem_Icc.1 (hT hx')
      exact Finset.mem_Icc.2 ⟨this.1, by omega⟩
  · rw [Finset.sum_insert hnot, hs]
    have hpw : 2 ^ (J + 1) = 2 ^ (J' + 1) * 2 ^ (t + 1) := by
      rw [hJ, show J' + (t + 1) + 1 = (J' + 1) + (t + 1) by ring, pow_add]
    have e1 : 2 ^ (J + 1) * w = 2 ^ (J' + 1) * (2 ^ (t + 1) * w) := by
      rw [hpw]
      ring
    rw [e1, hu]
    ring

/-- A weighted sum of a nonempty set of positive integers is positive. -/
theorem sum_pos_of_mem {T : Finset ℕ} {J a : ℕ} (hT : T ⊆ Finset.Icc 1 J) (ha : a ∈ T) :
    0 < ∑ j ∈ T, j * 2 ^ j := by
  have h1 : a * 2 ^ a ≤ ∑ j ∈ T, j * 2 ^ j :=
    Finset.single_le_sum (f := fun j => j * 2 ^ j) (fun _ _ => Nat.zero_le _) ha
  have h2 : 1 ≤ a := (Finset.mem_Icc.1 (hT ha)).1
  have h3 : 0 < 2 ^ a := by positivity
  have h4 : 1 * 1 ≤ a * 2 ^ a := Nat.mul_le_mul h2 h3
  omega

/-- Proposition `prop:roots`: if `T` represents `2^{J+1} w` and `a = min T`, then `1 ∉ T`
and the orbit of `(J, w)` under `Φ` ends at the root `(a - 1, 0)`. -/
theorem root_of_repr : ∀ (J w : ℕ) (T : Finset ℕ), IsState J w → T ⊆ Finset.Icc 1 J →
    ∑ j ∈ T, j * 2 ^ j = 2 ^ (J + 1) * w → ∀ a ∈ T, (∀ x ∈ T, a ≤ x) →
    1 ∉ T ∧ Reach (J, w) (a - 1, 0) := by
  intro J
  induction J using Nat.strong_induction_on with
  | _ J ih =>
    intro w T hst hT hs a ha hmin
    have hpos := sum_pos_of_mem hT ha
    have hw : 1 ≤ w := by
      by_contra hc
      have : w = 0 := by omega
      rw [this, Nat.mul_zero] at hs
      omega
    have hJ2 : 2 ≤ J := by have := hst.2; omega
    have h1 : 1 ∉ T := by
      have hX8 : 8 ∣ 2 ^ (J + 1) := by
        have h3 : 2 ^ 3 ∣ 2 ^ (J + 1) := pow_dvd_pow 2 (by omega)
        exact h3
      have h8 : 8 ∣ ∑ j ∈ T, j * 2 ^ j := by
        rw [hs]
        exact Dvd.dvd.mul_right hX8 w
      exact no_one hT h8
    refine ⟨h1, ?_⟩
    have hsucc : Succ J w := ⟨T, hT, hs⟩
    rcases (succ_iff_phi hst).1 hsucc with h0 | ⟨J', w', hphi, hsucc'⟩
    · omega
    · obtain ⟨T'', hT'', hs''⟩ := hsucc'
      obtain ⟨hsub, hsum⟩ := phi_repr hphi hT'' hs''
      have hEq : T = insert (J' + 1) T'' :=
        repr_unique J T _ hT hsub (hs.trans hsum.symm)
      have hlt := phi_lt hphi
      have hst' := phi_state hphi
      by_cases hne : T'' = ∅
      · rw [hne] at hs'' hEq
        rw [Finset.sum_empty] at hs''
        have hpos' : 0 < 2 ^ (J' + 1) := by positivity
        have hw' : w' = 0 := by
          rcases Nat.mul_eq_zero.1 hs''.symm with h0 | h0
          · omega
          · exact h0
        have haeq : a = J' + 1 := by
          rw [hEq] at ha
          simpa using ha
        rw [hw'] at hphi
        have : a - 1 = J' := by omega
        rw [this]
        exact Relation.ReflTransGen.single hphi
      · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.2 hne
        have hex : (T''.Nonempty) := ⟨b, hb⟩
        let a'' := T''.min' hex
        have ha'' : a'' ∈ T'' := Finset.min'_mem T'' hex
        have hmin'' : ∀ x ∈ T'', a'' ≤ x := fun x hx => Finset.min'_le T'' x hx
        obtain ⟨_, hreach⟩ := ih J' hlt w' T'' hst' hT'' hs'' a'' ha'' hmin''
        have hT''J : ∀ x ∈ T'', x ≤ J' := fun x hx => (Finset.mem_Icc.1 (hT'' hx)).2
        have haT : a ∈ T'' := by
          rw [hEq] at ha
          rcases Finset.mem_insert.1 ha with h | h
          · have h1' := hmin a'' (by rw [hEq]; exact Finset.mem_insert_of_mem ha'')
            have h2' := hT''J a'' ha''
            omega
          · exact h
        have hal : a = a'' := by
          have h1' := hmin a'' (by rw [hEq]; exact Finset.mem_insert_of_mem ha'')
          have h2' := hmin'' a haT
          omega
        rw [hal]
        exact Relation.ReflTransGen.head hphi hreach

/-- States with `w = 0` have no image under `Φ`. -/
theorem no_succ_root (a : ℕ) : ∀ b : ℕ × ℕ, ¬ (fun x y : ℕ × ℕ => Phi x.1 x.2 y.1 y.2) (a, 0) b := by
  intro b h
  obtain ⟨_, hw, _⟩ := h
  have h0 : (1 : ℕ) ≤ 0 := hw
  omega

theorem reach_root_unique {x y z : ℕ × ℕ} (hy : y.2 = 0) (hz : z.2 = 0) (hxy : Reach x y)
    (hxz : Reach x z) : y = z := by
  have hU : Relator.RightUnique (fun x y : ℕ × ℕ => Phi x.1 x.2 y.1 y.2) := by
    intro a b c h1 h2
    obtain ⟨hJ, hw⟩ := phi_unique h1 h2
    exact Prod.ext hJ hw
  have hnone : ∀ p : ℕ × ℕ, p.2 = 0 → ∀ b : ℕ × ℕ,
      ¬ (fun x y : ℕ × ℕ => Phi x.1 x.2 y.1 y.2) p b := by
    intro p hp b h
    obtain ⟨_, hw, _⟩ := h
    omega
  rcases Relation.ReflTransGen.total_of_right_unique hU hxy hxz with h | h
  · have := (Relation.reflTransGen_iff_eq (hnone y hy)).1 h
    exact this.symm
  · have := (Relation.reflTransGen_iff_eq (hnone z hz)).1 h
    exact this

/-- For a successful state of level `J ≥ 2` represented by `T`: the orbit ends at `(1, 0)`
if and only if `2 ∈ T`. -/
theorem reach_one_iff {J w : ℕ} {T : Finset ℕ} (hJ : 2 ≤ J) (hst : IsState J w)
    (hT : T ⊆ Finset.Icc 1 J) (hs : ∑ j ∈ T, j * 2 ^ j = 2 ^ (J + 1) * w) :
    Reach (J, w) (1, 0) ↔ 2 ∈ T := by
  constructor
  · intro hr
    by_cases hne : T = ∅
    · rw [hne, Finset.sum_empty] at hs
      have hpos : 0 < 2 ^ (J + 1) := by positivity
      have hw0 : w = 0 := by
        rcases Nat.mul_eq_zero.1 hs.symm with h0 | h0
        · omega
        · exact h0
      rw [hw0] at hr
      have hnone : ∀ b : ℕ × ℕ, ¬ (fun x y : ℕ × ℕ => Phi x.1 x.2 y.1 y.2) (J, 0) b :=
        no_succ_root J
      have := (Relation.reflTransGen_iff_eq hnone).1 hr
      have h1 : (1 : ℕ) = J := congrArg Prod.fst this
      omega
    · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.2 hne
      have hex : T.Nonempty := ⟨b, hb⟩
      have ha : T.min' hex ∈ T := Finset.min'_mem T hex
      have hmin : ∀ x ∈ T, T.min' hex ≤ x := fun x hx => Finset.min'_le T x hx
      obtain ⟨h1, hreach⟩ := root_of_repr J w T hst hT hs _ ha hmin
      have hu := reach_root_unique (x := (J, w)) (y := (T.min' hex - 1, 0)) (z := (1, 0))
        rfl rfl hreach hr
      have h2 : T.min' hex - 1 = 1 := congrArg Prod.fst hu
      have h3 : 1 ≤ T.min' hex := (Finset.mem_Icc.1 (hT ha)).1
      have h4 : T.min' hex = 2 := by omega
      rw [h4] at ha
      exact ha
  · intro h2
    have hmin2 : ∃ a ∈ T, ∀ x ∈ T, a ≤ x := by
      have hex : T.Nonempty := ⟨2, h2⟩
      exact ⟨T.min' hex, Finset.min'_mem T hex, fun x hx => Finset.min'_le T x hx⟩
    obtain ⟨a, ha, hmin⟩ := hmin2
    obtain ⟨h1, hreach⟩ := root_of_repr J w T hst hT hs a ha hmin
    have h3 : a ≤ 2 := hmin 2 h2
    have h4 : 1 ≤ a := (Finset.mem_Icc.1 (hT ha)).1
    have h5 : a ≠ 1 := fun h => h1 (by rw [← h]; exact ha)
    have h6 : a - 1 = 1 := by omega
    rw [h6] at hreach
    exact hreach

/-- The orbit of `(J, w)` ends at `(1, 0)` exactly for one of `w`, `J - 1 - w`. -/
theorem two_symm {J w : ℕ} (hJ : 2 ≤ J) (hw : w ∈ SJ J) :
    Reach (J, w) (1, 0) ↔ ¬ Reach (J, J - 1 - w) (1, 0) := by
  obtain ⟨hwJ, T, hT, hs⟩ := mem_SJ.1 hw
  obtain ⟨h1, hsum⟩ := symm_set hJ hwJ hT hs
  have hT' : Finset.Icc 1 J \ insert 1 T ⊆ Finset.Icc 1 J :=
    fun x hx => (Finset.mem_sdiff.1 hx).1
  have hst : IsState J w := ⟨by omega, hwJ⟩
  have hst' : IsState J (J - 1 - w) := ⟨by omega, by omega⟩
  rw [reach_one_iff hJ hst hT hs, reach_one_iff hJ hst' hT' hsum]
  have h2 : (2 : ℕ) ∈ Finset.Icc 1 J \ insert 1 T ↔ 2 ∉ T := by
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_Icc]
    constructor
    · rintro ⟨_, h⟩ h2T
      exact h (Or.inr h2T)
    · intro h
      refine ⟨⟨by omega, hJ⟩, ?_⟩
      rintro (h' | h')
      · omega
      · exact h h'
  rw [h2]
  tauto

/-- Proposition `prop:roots`: for `J ≥ 2`, exactly `N(J)/2` successful states of level `J` lie
in the tree of the root `(1, 0)`; in particular `N(J)` is even. -/
theorem roots_half {J : ℕ} (hJ : 2 ≤ J) :
    2 * ((SJ J).filter (fun w => Reach (J, w) (1, 0))).card = NJ J := by
  have hsplit : ((SJ J).filter (fun w => Reach (J, w) (1, 0))).card
      + ((SJ J).filter (fun w => ¬ Reach (J, w) (1, 0))).card = (SJ J).card :=
    card_split (SJ J) (fun w => Reach (J, w) (1, 0))
  have hcard : ((SJ J).filter (fun w => ¬ Reach (J, w) (1, 0))).card
      = ((SJ J).filter (fun w => Reach (J, w) (1, 0))).card := by
    symm
    apply Finset.card_bij (fun w _ => J - 1 - w)
    · intro w hw
      simp only [Finset.mem_filter] at hw ⊢
      obtain ⟨hwS, hP⟩ := hw
      obtain ⟨hwJ, hsw⟩ := mem_SJ.1 hwS
      refine ⟨mem_SJ.2 ⟨by omega, (succ_symm (by omega) hwJ).1 hsw⟩, ?_⟩
      exact (two_symm hJ hwS).1 hP
    · intro w1 hw1 w2 hw2 heq
      rw [Finset.mem_filter] at hw1 hw2
      have h1 := (mem_SJ.1 hw1.1).1
      have h2 := (mem_SJ.1 hw2.1).1
      have heq' : J - 1 - w1 = J - 1 - w2 := heq
      omega
    · intro v hv
      rw [Finset.mem_filter] at hv
      obtain ⟨hvS, hnP⟩ := hv
      obtain ⟨hvJ, hsv⟩ := mem_SJ.1 hvS
      have hwS : J - 1 - v ∈ SJ J :=
        mem_SJ.2 ⟨by omega, (succ_symm (by omega) hvJ).1 hsv⟩
      refine ⟨J - 1 - v, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨hwS, ?_⟩
        by_contra hc
        have h1 := (two_symm hJ hvS).2 hc
        exact hnP h1
      · show J - 1 - (J - 1 - v) = v
        omega
  unfold NJ
  omega

end SequenceNicolas.Roots
