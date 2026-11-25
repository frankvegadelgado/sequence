module

public import Mathlib
public import SequenceNicolas.PrimesBase
public import SequenceNicolas.PrimesRep
public import SequenceNicolas.PrimesStep

@[expose] public section

/-!
# The analogue for an arbitrary prime: `thm:primebottomup`

`Sset p K` is the finite set `S^{(p)}_K` of the `w` such that the `p`-state `(K, w)` is successful.
-/

namespace SequenceNicolas.Primes

open scoped Classical

variable {p : ℕ} [hp : Fact p.Prime]

/-- `S^{(p)}_K`. -/
noncomputable def Sset (p K : ℕ) : Finset ℕ := (Finset.range ((p - 1) * K + 1)).filter (fun w => Succp p K w)

theorem mem_Sset {K w : ℕ} : w ∈ Sset p K ↔ Succp p K w := by
  unfold Sset
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by have := succ_le h; omega, h⟩

omit hp in
theorem succ_zero_iff {w : ℕ} : Succp p 0 w ↔ w = 0 := by
  constructor
  · rintro ⟨d, _, he⟩
    have h0 : esum p d 0 = 0 := by simp [esum]
    rw [h0] at he
    simpa using he
  · rintro rfl
    exact succ_zero 0

/-- Theorem `thm:primebottomup` (1), the start. -/
theorem Sset_zero : Sset p 0 = {0} := by
  ext w
  rw [mem_Sset, succ_zero_iff, Finset.mem_singleton]

omit hp in
theorem InEp_succ {K V : ℕ} :
    InEp p (K + 1) V ↔ ∃ d R, d ≤ p - 1 ∧ InEp p K R ∧ V = R + d * tt p K := by
  constructor
  · rintro ⟨e, he, hV⟩
    exact ⟨e K, esum p e K, he K, ⟨e, he, rfl⟩, by rw [hV, esum_succ]⟩
  · rintro ⟨d, R, hd, ⟨e, he, hR⟩, hV⟩
    let dd : ℕ → ℕ := fun j => if j = K then d else e j
    have hdd : ∀ j, dd j ≤ p - 1 := by
      intro j
      by_cases h : j = K
      · simp only [dd, h, ↓reduceIte]; exact hd
      · simp only [dd, h, ↓reduceIte]; exact he j
    refine ⟨dd, hdd, ?_⟩
    have hc : esum p dd K = esum p e K := by
      apply esum_congr
      intro j hj
      have hne : j ≠ K := Nat.ne_of_lt hj
      simp only [dd, hne, ↓reduceIte]
    rw [esum_succ, hV, hR, hc]
    simp [dd]

/-- Theorem `thm:primebottomup` (1): the step from `K` to `K + 1`. -/
theorem succ_succ_iff {K w' : ℕ} :
    Succp p (K + 1) w' ↔
      ∃ w d, Succp p K w ∧ d ≤ p - 1 ∧ p * w' = w + d * ((p - 1) * K + p) := by
  have hP : 0 < p ^ K := pow_pos hp.out.pos K
  have hpow : p ^ (K + 1) = p ^ K * p := pow_succ _ _
  have htt : tt p K = p ^ K * ((p - 1) * K + p) := rfl
  have e1 : p ^ (K + 1) * w' = p ^ K * (p * w') := by rw [hpow]; ring
  have e2 : ∀ d : ℕ, d * tt p K = p ^ K * (d * ((p - 1) * K + p)) := by
    intro d
    rw [htt]; ring
  unfold Succp
  constructor
  · intro h
    obtain ⟨d, R, hd, hR, hV⟩ := InEp_succ.1 h
    have e2d := e2 d
    have hle : d * ((p - 1) * K + p) ≤ p * w' := by
      by_contra hc
      push Not at hc
      have := mlt hP hc
      omega
    obtain ⟨w, hw⟩ : ∃ w, p * w' = d * ((p - 1) * K + p) + w :=
      ⟨p * w' - d * ((p - 1) * K + p), by omega⟩
    have e3 : p ^ K * (p * w') = p ^ K * (d * ((p - 1) * K + p)) + p ^ K * w := by
      rw [hw, mul_add]
    have hRw : R = p ^ K * w := by omega
    refine ⟨w, d, ?_, hd, by omega⟩
    rw [← hRw]
    exact hR
  · rintro ⟨w, d, hw, hd, he⟩
    apply InEp_succ.2
    refine ⟨d, p ^ K * w, hd, hw, ?_⟩
    rw [e1, e2 d, he, mul_add]

/-- Theorem `thm:primebottomup` (1): distinct pairs `(w, d)` give distinct elements. -/
theorem succ_pair_inj {K w1 w2 d1 d2 : ℕ} (h1 : Succp p K w1) (h2 : Succp p K w2)
    (heq : w1 + d1 * ((p - 1) * K + p) = w2 + d2 * ((p - 1) * K + p)) :
    w1 = w2 ∧ d1 = d2 := by
  have hp1 := hp.out.one_lt
  have l1 := succ_le h1
  have l2 := succ_le h2
  have hlt1 : w1 < (p - 1) * K + p := by omega
  have hlt2 : w2 < (p - 1) * K + p := by omega
  generalize (p - 1) * K + p = u at heq hlt1 hlt2
  have hu : 0 < u := by omega
  have m1 : (w1 + d1 * u) % u = w1 := by
    rw [Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hlt1
  have m2 : (w2 + d2 * u) % u = w2 := by
    rw [Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hlt2
  have hw : w1 = w2 := by rw [← m1, heq, m2]
  refine ⟨hw, ?_⟩
  have : d1 * u = d2 * u := by omega
  exact Nat.eq_of_mul_eq_mul_right hu this

/-- The number of successful states: `N_p(K + 1)` as a sum over `S_K`. -/
theorem N_succ (K : ℕ) :
    (Sset p (K + 1)).card =
      ∑ w ∈ Sset p K,
        ((Finset.range p).filter (fun d => p ∣ w + d * ((p - 1) * K + p))).card := by
  obtain ⟨T, hTdef⟩ : ∃ T : Finset (ℕ × ℕ), T = ((Sset p K) ×ˢ (Finset.range p)).filter
      (fun x : ℕ × ℕ => p ∣ x.1 + x.2 * ((p - 1) * K + p)) := ⟨_, rfl⟩
  have hTm : ∀ x : ℕ × ℕ, x ∈ T ↔
      (Succp p K x.1 ∧ x.2 < p) ∧ p ∣ x.1 + x.2 * ((p - 1) * K + p) := by
    intro x
    rw [hTdef, Finset.mem_filter, Finset.mem_product, mem_Sset, Finset.mem_range]
  have hT : Sset p (K + 1) =
      T.image (fun x : ℕ × ℕ => (x.1 + x.2 * ((p - 1) * K + p)) / p) := by
    ext w'
    rw [mem_Sset, succ_succ_iff, Finset.mem_image]
    constructor
    · rintro ⟨w, d, hw, hd, he⟩
      refine ⟨(w, d), ?_, ?_⟩
      · rw [hTm]
        exact ⟨⟨hw, by have := hp.out.pos; omega⟩, ⟨w', he.symm⟩⟩
      · show (w + d * ((p - 1) * K + p)) / p = w'
        rw [← he]
        exact Nat.mul_div_cancel_left w' hp.out.pos
    · rintro ⟨⟨w, d⟩, hx, hxe⟩
      rw [hTm] at hx
      obtain ⟨⟨hw, hd⟩, hdv⟩ := hx
      refine ⟨w, d, hw, by omega, ?_⟩
      have hxe' : (w + d * ((p - 1) * K + p)) / p = w' := hxe
      rw [← hxe']
      exact Nat.mul_div_cancel' hdv
  rw [hT, Finset.card_image_of_injOn]
  · rw [hTdef, Finset.card_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro w _
    exact (Finset.card_filter _ _).symm
  · intro x hx y hy hxy
    have hx' := (hTm x).1 hx
    have hy' := (hTm y).1 hy
    have h1 : x.1 + x.2 * ((p - 1) * K + p) = y.1 + y.2 * ((p - 1) * K + p) := by
      have hxy' : (x.1 + x.2 * ((p - 1) * K + p)) / p = (y.1 + y.2 * ((p - 1) * K + p)) / p := hxy
      rw [← Nat.mul_div_cancel' hx'.2, ← Nat.mul_div_cancel' hy'.2, hxy']
    obtain ⟨a1, a2⟩ := succ_pair_inj hx'.1.1 hy'.1.1 h1
    exact Prod.ext a1 a2

omit hp in
/-- `p ∣ a + b ↔ p ∣ a` when `p ∣ b`. -/
theorem dvd_add_cancel {a b : ℕ} (h : p ∣ b) : p ∣ a + b ↔ p ∣ a := by
  obtain ⟨e, he⟩ := h
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c - e, ?_⟩
    rw [mul_tsub]
    omega
  · rintro ⟨c, hc⟩
    exact ⟨c + e, by rw [mul_add]; omega⟩

/-- The digit `d` is determined modulo `p` when `p ∤ u`. -/
theorem digit_unique_aux {u : ℕ} (hu : ¬ p ∣ u) (w : ℕ) :
    ∃! d, d ≤ p - 1 ∧ p ∣ w + d * u := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hp1 := hp.out.one_lt
  have hu0 : (u : ZMod p) ≠ 0 := fun h => hu ((CharP.cast_eq_zero_iff (ZMod p) p u).1 h)
  have hc : ∀ a b : ℕ, p ∣ a + b * u ↔ (a : ZMod p) + (b : ZMod p) * (u : ZMod p) = 0 := by
    intro a b
    rw [← CharP.cast_eq_zero_iff (ZMod p) p]
    push_cast
    exact Iff.rfl
  have hval : ∀ a b : ℕ, (a : ZMod p) = (b : ZMod p) → a % p = b % p := by
    intro a b h
    have := congrArg ZMod.val h
    rw [ZMod.val_natCast, ZMod.val_natCast] at this
    exact this
  set d : ℕ := ((-(w : ZMod p)) / (u : ZMod p)).val with hd
  have hdlt : d < p := ZMod.val_lt _
  have hdcast : (d : ZMod p) = (-(w : ZMod p)) / (u : ZMod p) := by
    rw [hd]
    exact ZMod.natCast_zmod_val _
  have hdiv : (-(w : ZMod p)) / (u : ZMod p) * (u : ZMod p) = -(w : ZMod p) := by
    exact div_mul_cancel₀ _ hu0
  refine ⟨d, ⟨by omega, ?_⟩, ?_⟩
  · rw [hc, hdcast, hdiv]
    exact add_neg_cancel _
  · rintro y ⟨hy1, hy2⟩
    have h1 := (hc w y).1 hy2
    have h2 : (w : ZMod p) + (d : ZMod p) * (u : ZMod p) = 0 := by
      rw [hdcast, hdiv]
      exact add_neg_cancel _
    have h3 : (y : ZMod p) * (u : ZMod p) = (d : ZMod p) * (u : ZMod p) := by
      have hyu : (y : ZMod p) * (u : ZMod p) = -(w : ZMod p) := eq_neg_of_add_eq_zero_right h1
      have hdu : (d : ZMod p) * (u : ZMod p) = -(w : ZMod p) := eq_neg_of_add_eq_zero_right h2
      rw [hyu, hdu]
    have h4 : (y : ZMod p) = (d : ZMod p) := mul_right_cancel₀ hu0 h3
    have h5 := hval y d h4
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hdlt] at h5
    exact h5

theorem not_dvd_u {K : ℕ} (hK : ¬ p ∣ K) : ¬ p ∣ (p - 1) * K + p := by
  have hp1 := hp.out.one_lt
  intro h
  obtain ⟨c, hc⟩ := h
  have h1 : p ∣ (p - 1) * K := ⟨c - 1, by
    rw [Nat.mul_sub_one]; omega⟩
  rcases hp.out.dvd_mul.1 h1 with h2 | h2
  · have := Nat.le_of_dvd (by omega) h2
    omega
  · exact hK h2

/-- Theorem `thm:primebottomup` (2): `N_p(K + 1) = N_p(K)` when `p ∤ K`. -/
theorem N_succ_not_dvd {K : ℕ} (hK : ¬ p ∣ K) : (Sset p (K + 1)).card = (Sset p K).card := by
  have hp1 := hp.out.pos
  rw [N_succ]
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro w _
  obtain ⟨d, ⟨hd1, hd2⟩, huniq⟩ := digit_unique_aux (not_dvd_u hK) w
  apply Finset.card_eq_one.2
  refine ⟨d, ?_⟩
  ext x
  rw [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hdv⟩
    exact huniq x ⟨by omega, hdv⟩
  · rintro rfl
    exact ⟨by omega, hd2⟩

/-- Theorem `thm:primebottomup` (2): for each `w` exactly one digit `d`. -/
theorem digit_unique {K : ℕ} (hK : ¬ p ∣ K) (w : ℕ) :
    ∃! d, d ≤ p - 1 ∧ p ∣ w + d * ((p - 1) * K + p) :=
  digit_unique_aux (not_dvd_u hK) w

/-- Theorem `thm:primebottomup` (3): the count when `p ∣ K`. -/
theorem N_succ_dvd {K : ℕ} (hK : p ∣ K) :
    (Sset p (K + 1)).card = p * ((Sset p K).filter (fun w => p ∣ w)).card := by
  have hpu : p ∣ (p - 1) * K + p := by
    obtain ⟨k, hk⟩ := hK
    exact ⟨(p - 1) * k + 1, by rw [hk]; ring⟩
  rw [N_succ]
  calc ∑ w ∈ Sset p K,
        ((Finset.range p).filter (fun d => p ∣ w + d * ((p - 1) * K + p))).card
      = ∑ w ∈ Sset p K, p * (if p ∣ w then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro w _
        have hdd : ∀ d : ℕ, (p ∣ w + d * ((p - 1) * K + p) ↔ p ∣ w) := by
          intro d
          exact dvd_add_cancel (Dvd.dvd.mul_left hpu d)
        by_cases h : p ∣ w
        · simp only [h, ↓reduceIte, mul_one]
          have : (Finset.range p).filter (fun d => p ∣ w + d * ((p - 1) * K + p)) =
              Finset.range p := by
            apply Finset.filter_true_of_mem
            intro d _
            exact (hdd d).2 h
          rw [this, Finset.card_range]
        · simp only [h, ↓reduceIte, mul_zero]
          apply Finset.card_eq_zero.2
          apply Finset.filter_eq_empty_iff.2
          intro d _ hd
          exact h ((hdd d).1 hd)
    _ = p * ∑ w ∈ Sset p K, (if p ∣ w then 1 else 0) := (Finset.mul_sum _ _ _).symm
    _ = p * ((Sset p K).filter (fun w => p ∣ w)).card := by rw [Finset.card_filter]

/-- Theorem `thm:primebottomup` (3): the description of `S_{K+1}` as a union of translates. -/
theorem succ_dvd_iff {k w' : ℕ} :
    Succp p (p * k + 1) w' ↔
      ∃ b d, d ≤ p - 1 ∧ Succp p (p * k) (p * b) ∧ w' = b + d * ((p - 1) * k + 1) := by
  have hp0 := hp.out.pos
  have hu : (p - 1) * (p * k) + p = p * ((p - 1) * k + 1) := by ring
  rw [succ_succ_iff, hu]
  constructor
  · rintro ⟨w, d, hw, hd, he⟩
    have hdv : p ∣ w := by
      have : p ∣ w + d * (p * ((p - 1) * k + 1)) := ⟨w', he.symm⟩
      exact (dvd_add_cancel (Dvd.dvd.mul_left (dvd_mul_right p _) d)).1 this
    obtain ⟨b, hb⟩ := hdv
    refine ⟨b, d, hd, ?_, ?_⟩
    · rw [← hb]; exact hw
    · apply Nat.eq_of_mul_eq_mul_left hp0
      rw [he, hb]
      ring
  · rintro ⟨b, d, hd, hb, he⟩
    refine ⟨p * b, d, hb, hd, ?_⟩
    rw [he]
    ring

/-- Theorem `thm:primebottomup` (3): the translates are disjoint. -/
theorem succ_dvd_inj {k b1 b2 d1 d2 : ℕ} (h1 : Succp p (p * k) (p * b1))
    (h2 : Succp p (p * k) (p * b2))
    (heq : b1 + d1 * ((p - 1) * k + 1) = b2 + d2 * ((p - 1) * k + 1)) : b1 = b2 ∧ d1 = d2 := by
  have hp0 := hp.out.pos
  have hu : (p - 1) * (p * k) + p = p * ((p - 1) * k + 1) := by ring
  have := succ_pair_inj h1 h2 (K := p * k) (d1 := d1) (d2 := d2) (by
    rw [hu]
    have h3 : p * (b1 + d1 * ((p - 1) * k + 1)) = p * (b2 + d2 * ((p - 1) * k + 1)) := by
      rw [heq]
    calc p * b1 + d1 * (p * ((p - 1) * k + 1)) = p * (b1 + d1 * ((p - 1) * k + 1)) := by ring
      _ = p * (b2 + d2 * ((p - 1) * k + 1)) := h3
      _ = p * b2 + d2 * (p * ((p - 1) * k + 1)) := by ring)
  exact ⟨Nat.eq_of_mul_eq_mul_left hp0 this.1, this.2⟩

/-! ### Symmetry -/

theorem esum_compl {d : ℕ → ℕ} (hd : ∀ i, d i ≤ p - 1) (K : ℕ) :
    esum p (fun i => p - 1 - d i) K + esum p d K = K * (p - 1) * p ^ K := by
  rw [← sum_pm1]
  unfold esum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have := hd i
  show (p - 1 - d i) * tt p i + d i * tt p i = (p - 1) * tt p i
  rw [← add_mul]
  congr 1
  omega

/-- Theorem `thm:primebottomup` (4): symmetry. -/
theorem succ_symm {K w : ℕ} (h : Succp p K w) : Succp p K ((p - 1) * K - w) := by
  have hw := succ_le h
  obtain ⟨d, hd, he⟩ := h
  refine ⟨fun i => p - 1 - d i, fun i => Nat.sub_le _ _, ?_⟩
  have hc := esum_compl hd K
  obtain ⟨c, hcc⟩ : ∃ c, (p - 1) * K = w + c := ⟨(p - 1) * K - w, by omega⟩
  have f : K * (p - 1) * p ^ K = p ^ K * w + p ^ K * c := by
    rw [show K * (p - 1) * p ^ K = p ^ K * ((p - 1) * K) by ring, hcc, mul_add]
  have hcw : (p - 1) * K - w = c := by omega
  rw [hcw]
  omega

theorem succ_symm_iff {K w : ℕ} (h : w ≤ (p - 1) * K) :
    Succp p K w ↔ Succp p K ((p - 1) * K - w) := by
  constructor
  · exact succ_symm
  · intro h2
    have := succ_symm h2
    have e : (p - 1) * K - ((p - 1) * K - w) = w := by omega
    rw [e] at this
    exact this

/-- The last statement of `thm:primebottomup`. -/
theorem Ap_iff_Sset {a K : ℕ} (hK : bp p K = a + 1) :
    Ap p a ↔ p ^ gexp p K % ((p - 1) * K + p) ≤ (p - 1) * K ∧
      p ^ gexp p K % ((p - 1) * K + p) ∈ Sset p K := by
  rw [primestep_one hK, mem_Sset]

end SequenceNicolas.Primes
