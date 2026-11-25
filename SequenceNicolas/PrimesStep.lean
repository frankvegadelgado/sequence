module

public import Mathlib
public import SequenceNicolas.PrimesBase
public import SequenceNicolas.PrimesRep

@[expose] public section

/-!
# The analogue for an arbitrary prime: the recursion `thm:primestep`

`Succp p K w` says that the `p`-state `(K, w)` is successful, `p^K w ∈ 𝓔^{(p)}_K`; the bound
`w ≤ (p-1)K` of a `p`-state is a consequence (`succ_le`).
-/

namespace SequenceNicolas.Primes

open scoped Classical

/-- The `p`-state `(K, w)` is successful: `p^K w ∈ 𝓔^{(p)}_K`. -/
def Succp (p K w : ℕ) : Prop := InEp p K (p ^ K * w)

variable {p : ℕ} [hp : Fact p.Prime]

theorem mlt {a b c : ℕ} (ha : 0 < a) (h : b < c) : a * b < a * c := by
  exact Nat.mul_lt_mul_of_pos_left h ha

theorem tt_mono_succ (i : ℕ) : tt p i ≤ tt p (i + 1) := by
  unfold tt
  have h1 : p ^ (i + 1) = p ^ i * p := pow_succ _ _
  have hP : 0 < p ^ i := pow_pos hp.out.pos i
  have h2 : (p - 1) * i ≤ (p - 1) * (i + 1) := Nat.mul_le_mul_left _ (by omega)
  have h3 : p ^ i ≤ p ^ i * p := Nat.le_mul_of_pos_right _ hp.out.pos
  calc p ^ i * ((p - 1) * i + p) ≤ p ^ i * ((p - 1) * (i + 1) + p) :=
        Nat.mul_le_mul_left _ (by omega)
    _ ≤ p ^ i * p * ((p - 1) * (i + 1) + p) := Nat.mul_le_mul_right _ h3
    _ = p ^ (i + 1) * ((p - 1) * (i + 1) + p) := by rw [h1]

theorem tt_mono : Monotone (tt p) := monotone_nat_of_le_succ tt_mono_succ

omit hp in
theorem esum_congr {d d' : ℕ → ℕ} {K : ℕ} (h : ∀ j, j < K → d j = d' j) :
    esum p d K = esum p d' K := by
  unfold esum
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j (Finset.mem_range.1 hj)]

omit hp in
theorem esum_zero_ext {d : ℕ → ℕ} {i : ℕ} (hz : ∀ j, i ≤ j → d j = 0) :
    ∀ M, i ≤ M → esum p d M = esum p d i := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => rfl
  | succ M hM ih =>
    rw [esum_succ, hz M hM, ih]
    simp

omit hp in
theorem esum_ne_zero_digit {d : ℕ → ℕ} {M : ℕ} (h : esum p d M ≠ 0) :
    ∃ i, i < M ∧ d i ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  unfold esum
  apply Finset.sum_eq_zero
  intro i hi
  rw [hc i (Finset.mem_range.1 hi)]
  simp

theorem succ_le {K w : ℕ} (h : Succp p K w) : w ≤ (p - 1) * K := by
  obtain ⟨d, hd, he⟩ := h
  have h1 := esum_le hd K
  rw [← he] at h1
  have hP : 0 < p ^ K := pow_pos hp.out.pos K
  have h2 : w * p ^ K ≤ ((p - 1) * K) * p ^ K := by
    have e1 : w * p ^ K = p ^ K * w := mul_comm _ _
    have e2 : ((p - 1) * K) * p ^ K = K * (p - 1) * p ^ K := by ring
    rw [e1, e2]
    exact h1
  exact Nat.le_of_mul_le_mul_right h2 hP

omit hp in
theorem succ_zero (K : ℕ) : Succp p K 0 := by
  refine ⟨fun _ => 0, fun _ => Nat.zero_le _, ?_⟩
  simp [esum]

theorem InEp_lt {K V : ℕ} (h : InEp p K V) : V < tt p K := by
  obtain ⟨d, hd, he⟩ := h
  rw [he]
  exact esum_lt hd K

/-- The key decomposition (Theorem `thm:primes` (2)): if `t_i ≤ V < t_{i+1}`, a representation of
`V` in `𝓔^{(p)}_M`, `M ≥ i + 1`, has largest index `i`. -/
theorem InEp_top {i V M : ℕ} (h1 : tt p i ≤ V) (h2 : V < tt p (i + 1)) (hM : i + 1 ≤ M) :
    InEp p M V ↔ V / tt p i ≤ p - 1 ∧ InEp p i (V % tt p i) := by
  have hpos := tt_pos (p := p) i
  constructor
  · rintro ⟨d, hd, hV⟩
    have hne : esum p d M ≠ 0 := by
      rw [← hV]
      omega
    obtain ⟨i', hi', hdi'⟩ := esum_ne_zero_digit hne
    obtain ⟨m, hm, hdm, hem⟩ := esum_trim (p := p) d M ⟨i', hi', hdi'⟩
    rw [hem] at hV
    have hmV : tt p m ≤ V := by
      rw [hV, esum_succ]
      have : tt p m ≤ d m * tt p m := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hdm)
      omega
    have hmi : m = i := by
      rcases lt_trichotomy m i with hl | he | hg
      · exfalso
        have a1 : V < tt p (m + 1) := by
          rw [hV]
          exact esum_lt hd (m + 1)
        have a2 : tt p (m + 1) ≤ tt p i := tt_mono (by omega)
        omega
      · exact he
      · exfalso
        have a2 : tt p (i + 1) ≤ tt p m := tt_mono (by omega)
        omega
    subst hmi
    obtain ⟨t1, t2⟩ := top_digit hd m
    refine ⟨by rw [hV, ← t1]; exact hd m, ?_⟩
    rw [hV, t2]
    exact ⟨d, hd, rfl⟩
  · rintro ⟨hd0, d', hd', he⟩
    let dd : ℕ → ℕ := fun j => if j < i then d' j else if j = i then V / tt p i else 0
    have hdd : ∀ j, dd j ≤ p - 1 := by
      intro j
      by_cases hj : j < i
      · simp only [dd, hj, ↓reduceIte]; exact hd' j
      · by_cases hji : j = i
        · subst hji; simpa [dd] using hd0
        · simp only [dd, hj, hji, ↓reduceIte]; exact Nat.zero_le _
    refine ⟨dd, hdd, ?_⟩
    have hz : ∀ j, i + 1 ≤ j → dd j = 0 := by
      intro j hj
      have h1 : ¬ j < i := by omega
      have h2 : j ≠ i := by omega
      simp only [dd, h1, h2, ↓reduceIte]
    rw [esum_zero_ext hz M hM, esum_succ]
    have hc : esum p dd i = esum p d' i := by
      apply esum_congr
      intro j hj
      simp only [dd, hj, ↓reduceIte]
    have hdi : dd i = V / tt p i := by
      simp only [dd]
      simp
    rw [hc, hdi, ← he]
    have := Nat.mod_add_div V (tt p i)
    rw [mul_comm] at this
    omega

theorem Ap_iff' (a : ℕ) : Ap p a ↔ ∃ M, InEp p M (p ^ (a + 1)) := by
  rw [Ap_iff]
  constructor
  · rintro ⟨K, d, hd, _, he⟩
    exact ⟨K, d, hd, he⟩
  · rintro ⟨M, d, hd, he⟩
    have hpos : 0 < p ^ (a + 1) := pow_pos hp.out.pos _
    obtain ⟨i, hi, hdi⟩ := esum_ne_zero_digit (d := d) (M := M)
      (by intro h0; rw [h0] at he; exact absurd he hpos.ne')
    exact ⟨M, d, hd, ⟨i, hi, hdi⟩, he⟩

/-- Bounds of `p^{g(K)}`. -/
theorem cand_data (K : ℕ) :
    (p - 1) * K + p ≤ p ^ gexp p K ∧ p ^ gexp p K ≤ p * ((p - 1) * (K + 1)) := by
  obtain ⟨s1, s2⟩ := gexp_spec (p := p) K
  have hp1 := hp.out.one_lt
  have e : (p - 1) * (K + 1) = (p - 1) * K + (p - 1) := by ring
  refine ⟨by omega, ?_⟩
  obtain ⟨g', hg'⟩ : ∃ g', gexp p K = g' + 1 := ⟨gexp p K - 1, by omega⟩
  rw [hg', pow_succ']
  by_cases h0 : g' = 0
  · rw [h0]
    simp only [pow_zero, mul_one]
    have : 1 ≤ (p - 1) * (K + 1) := Nat.mul_pos (by omega) (by omega)
    nlinarith
  · have hlt : p ^ g' < (p - 1) * (K + 1) + 1 := by
      by_contra hc
      push Not at hc
      have := gexp_min (p := p) (K := K) (g := g') (by omega) hc
      omega
    have : p ^ g' ≤ (p - 1) * (K + 1) := by omega
    exact Nat.mul_le_mul_left p this

/-- Theorem `thm:primestep` (1). -/
theorem primestep_one {a K : ℕ} (hK : bp p K = a + 1) :
    Ap p a ↔ p ^ gexp p K % ((p - 1) * K + p) ≤ (p - 1) * K ∧
      Succp p K (p ^ gexp p K % ((p - 1) * K + p)) := by
  obtain ⟨c1, c2⟩ := cand_data (p := p) K
  have hV : p ^ (a + 1) = p ^ K * p ^ gexp p K := by
    rw [← pow_add]
    unfold bp at hK
    rw [← hK]
  set u := (p - 1) * K + p with hu
  set g := gexp p K with hg
  have hP : 0 < p ^ K := pow_pos hp.out.pos K
  have hmod : p ^ (a + 1) % tt p K = p ^ K * (p ^ g % u) := by
    rw [hV]
    exact Nat.mul_mod_mul_left _ _ _
  have hdiv : p ^ (a + 1) / tt p K = p ^ g / u := by
    rw [hV]
    exact Nat.mul_div_mul_left _ _ hP
  have hdlt : p ^ g / u ≤ p - 1 := by
    have hupos : 0 < u := by have := hp.out.pos; omega
    have : p ^ g < p * u := by
      have e : (p - 1) * (K + 1) = (p - 1) * K + (p - 1) := by ring
      have hp1 := hp.out.one_lt
      have : p * ((p - 1) * (K + 1)) < p * u := mlt hp.out.pos (by omega)
      omega
    have h2 : p ^ g / u < p := (Nat.div_lt_iff_lt_mul hupos).2 this
    omega
  have h1 : tt p K ≤ p ^ (a + 1) := by
    rw [hV]
    unfold tt
    exact Nat.mul_le_mul_left _ c1
  have h2 : p ^ (a + 1) < tt p (K + 1) := by
    rw [hV]
    unfold tt
    have e1 : p ^ (K + 1) = p ^ K * p := pow_succ _ _
    have hp1 := hp.out.one_lt
    have e : (p - 1) * (K + 1) = (p - 1) * K + (p - 1) := by ring
    have h3 : p ^ g < p * ((p - 1) * (K + 1) + p) := by
      have := Nat.mul_le_mul_left p (show (p - 1) * (K + 1) ≤ (p - 1) * (K + 1) + p by omega)
      have := Nat.mul_pos hp.out.pos hp.out.pos
      nlinarith
    rw [e1]
    calc p ^ K * p ^ g < p ^ K * (p * ((p - 1) * (K + 1) + p)) := mlt hP h3
      _ = p ^ K * p * ((p - 1) * (K + 1) + p) := by ring
  rw [Ap_iff']
  constructor
  · rintro ⟨M, hM⟩
    have hMK : K + 1 ≤ M := by
      by_contra hc
      push Not at hc
      have a1 := InEp_lt hM
      have a2 : tt p M ≤ tt p K := tt_mono (by omega)
      omega
    have := (InEp_top h1 h2 hMK).1 hM
    rw [hmod] at this
    exact ⟨succ_le this.2, this.2⟩
  · rintro ⟨_, hS⟩
    refine ⟨K + 1, (InEp_top h1 h2 (le_refl _)).2 ⟨by rw [hdiv]; exact hdlt, ?_⟩⟩
    rw [hmod]
    exact hS

/-! ### Theorem `thm:primestep` (2) -/

/-- The condition defining `s`. -/
def Pstep (p K w σ : ℕ) : Prop := 1 ≤ σ ∧ (p - 1) * (K - σ) + p ≤ p ^ σ * w

theorem pstep_top {K w : ℕ} (hK : 1 ≤ K) (hw : 1 ≤ w) : Pstep p K w K := by
  refine ⟨hK, ?_⟩
  have h1 : p ≤ p ^ K := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ K := Nat.pow_le_pow_right hp.out.pos hK
  have h2 : p ^ K ≤ p ^ K * w := Nat.le_mul_of_pos_right _ hw
  rw [Nat.sub_self, Nat.mul_zero, Nat.zero_add]
  omega

theorem exists_step {K w : ℕ} (hK : 1 ≤ K) (hw : 1 ≤ w) : ∃ σ, Pstep p K w σ :=
  ⟨K, pstep_top hK hw⟩

/-- The least `s ≥ 1` with `p^s w ≥ (p - 1)(K - s) + p`. -/
noncomputable def sstep (p K w : ℕ) : ℕ :=
  if h : ∃ σ, Pstep p K w σ then Nat.find h else 0

omit hp in
theorem sstep_spec {K w : ℕ} (h : ∃ σ, Pstep p K w σ) : Pstep p K w (sstep p K w) := by
  unfold sstep
  split_ifs
  exact Nat.find_spec h

omit hp in
theorem sstep_lt {K w σ : ℕ} (h : ∃ σ, Pstep p K w σ) (hσ : σ < sstep p K w) :
    ¬ Pstep p K w σ := by
  unfold sstep at hσ
  split_ifs at hσ
  exact Nat.find_min h hσ

omit hp in
theorem sstep_le {K w σ : ℕ} (h : Pstep p K w σ) : sstep p K w ≤ σ := by
  unfold sstep
  split_ifs with h'
  · exact Nat.find_min' _ h
  · exact absurd ⟨σ, h⟩ h'

/-- Theorem `thm:primestep` (2). -/
theorem primestep_two {K w s : ℕ} (hw1 : 1 ≤ w) (hw : w ≤ (p - 1) * K)
    (hs : s = sstep p K w) :
    1 ≤ s ∧ s ≤ K ∧
      (Succp p K w ↔
        p ^ s * w / ((p - 1) * (K - s) + p) ≤ p - 1 ∧
        p ^ s * w % ((p - 1) * (K - s) + p) ≤ (p - 1) * (K - s) ∧
        Succp p (K - s) (p ^ s * w % ((p - 1) * (K - s) + p))) := by
  have hp1 := hp.out.one_lt
  have hK1 : 1 ≤ K := by
    by_contra hc
    have h0 : K = 0 := by omega
    rw [h0, Nat.mul_zero] at hw
    omega
  have hex := exists_step (p := p) hK1 hw1
  obtain ⟨hs1, hs2⟩ := sstep_spec hex
  rw [← hs] at hs1 hs2
  have hsK : s ≤ K := by
    rw [hs]
    exact sstep_le (pstep_top hK1 hw1)
  obtain ⟨i, hi⟩ : ∃ i, K = i + s := ⟨K - s, by omega⟩
  have hiK : K - s = i := by omega
  rw [hiK] at hs2 ⊢
  have hlow : p ^ (s - 1) * w < (p - 1) * (i + 1) + p := by
    by_cases h1 : s = 1
    · have hK' : K = i + 1 := by omega
      rw [hK'] at hw
      rw [h1, Nat.sub_self, pow_zero, one_mul]
      omega
    · have hm := sstep_lt (p := p) (K := K) (w := w) (σ := s - 1) hex (by rw [← hs]; omega)
      unfold Pstep at hm
      have h3 := Nat.lt_of_not_le (not_and.1 hm (by omega))
      have h4 : K - (s - 1) = i + 1 := by omega
      rw [h4] at h3
      exact h3
  have hP : 0 < p ^ i := pow_pos hp.out.pos i
  have hVK : p ^ K * w = p ^ i * (p ^ s * w) := by
    rw [hi]; ring
  have htt : tt p i = p ^ i * ((p - 1) * i + p) := rfl
  have h1 : tt p i ≤ p ^ K * w := by
    rw [hVK, htt]
    exact Nat.mul_le_mul_left _ hs2
  have hsp : p ^ s * w = p * (p ^ (s - 1) * w) := by
    obtain ⟨t, ht⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    rw [ht, Nat.add_sub_cancel]
    ring
  have h2 : p ^ K * w < tt p (i + 1) := by
    rw [hVK]
    unfold tt
    rw [hsp, pow_succ]
    have h5 := mlt hp.out.pos hlow
    have h6 := mlt hP h5
    calc p ^ i * (p * (p ^ (s - 1) * w)) < p ^ i * (p * ((p - 1) * (i + 1) + p)) := h6
      _ = p ^ i * p * ((p - 1) * (i + 1) + p) := by ring
  have hmod : p ^ K * w % tt p i = p ^ i * (p ^ s * w % ((p - 1) * i + p)) := by
    rw [hVK, htt]
    exact Nat.mul_mod_mul_left _ _ _
  have hdiv : p ^ K * w / tt p i = p ^ s * w / ((p - 1) * i + p) := by
    rw [hVK, htt]
    exact Nat.mul_div_mul_left _ _ hP
  refine ⟨hs1, hsK, ?_⟩
  unfold Succp
  rw [InEp_top h1 h2 (by omega), hdiv, hmod]
  constructor
  · rintro ⟨a, b⟩
    exact ⟨a, succ_le b, b⟩
  · rintro ⟨a, _, b⟩
    exact ⟨a, b⟩

end SequenceNicolas.Primes
