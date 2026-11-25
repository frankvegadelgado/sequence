module

public import Mathlib
public import SequenceNicolas.Core
public import SequenceNicolas.Recursion

@[expose] public section

/-!
# Residues of powers of two, non-members, one-step exponents and the families of Nicolas

This module formalizes Lemma `lem:order`, Theorem `thm:nonmembers`, Theorem `thm:firststep` and
Proposition `prop:nicolasfamilies` of the paper (the explicit members of Theorem `thm:members` are
in `SequenceNicolas.Core`).
-/

namespace SequenceNicolas.Families

open SequenceNicolas.Recursion

/-! ### Lemma `lem:order` -/

theorem pow_two_m (m : ℕ) : 2 ^ (2 * m) ≡ 1 [MOD 2 ^ m + 1] := by
  have hX : 0 < 2 ^ m := by positivity
  obtain ⟨Y, hY⟩ : ∃ Y, 2 ^ m = Y + 1 := ⟨2 ^ m - 1, by omega⟩
  have h1 : 2 ^ (2 * m) = (2 ^ m + 1) * Y + 1 := by
    have : 2 ^ (2 * m) = 2 ^ m * 2 ^ m := by rw [two_mul, pow_add]
    rw [this, hY]
    ring
  have hd : (2 ^ m + 1) ∣ 2 ^ (2 * m) - 1 := ⟨Y, by omega⟩
  have hle : 1 ≤ 2 ^ (2 * m) := Nat.one_le_two_pow
  exact ((Nat.modEq_iff_dvd' hle).2 hd).symm

theorem pow_period (m q : ℕ) : 2 ^ (2 * m * q) ≡ 1 [MOD 2 ^ m + 1] := by
  have h := (pow_two_m m).pow q
  rw [one_pow, ← pow_mul] at h
  exact h

theorem pow_neg {m l : ℕ} (hl : l < m) : 2 ^ m * 2 ^ l ≡ (2 ^ m + 1) - 2 ^ l [MOD 2 ^ m + 1] := by
  have hle : 2 ^ l ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hl.le
  have hL : 2 ^ m * 2 ^ l + 2 ^ l ≡ 0 [MOD 2 ^ m + 1] :=
    (Nat.modEq_zero_iff_dvd).2 ⟨2 ^ l, by ring⟩
  have hR : (2 ^ m + 1 - 2 ^ l) + 2 ^ l ≡ 0 [MOD 2 ^ m + 1] :=
    (Nat.modEq_zero_iff_dvd).2 ⟨1, by omega⟩
  exact Nat.ModEq.add_right_cancel' (2 ^ l) (hL.trans hR.symm)

/-- Lemma `lem:order` (1), first case. -/
theorem order_one {m q l : ℕ} (_hl : l < m) : 2 ^ (2 * m * q + l) ≡ 2 ^ l [MOD 2 ^ m + 1] := by
  have h := (pow_period m q).mul_right (2 ^ l)
  rw [one_mul, ← pow_add] at h
  exact h

/-- Lemma `lem:order` (1), second case. -/
theorem order_two {m q l : ℕ} (hl : l < m) :
    2 ^ (2 * m * q + m + l) ≡ (2 ^ m + 1) - 2 ^ l [MOD 2 ^ m + 1] := by
  have h1 := (pow_period m q).mul_right (2 ^ m * 2 ^ l)
  rw [one_mul] at h1
  have h2 := h1.trans (pow_neg hl)
  have e : 2 ^ (2 * m * q + m + l) = 2 ^ (2 * m * q) * (2 ^ m * 2 ^ l) := by
    rw [pow_add, pow_add, mul_assoc]
  rw [e]
  exact h2

/-- Lemma `lem:order` (2): the residues `2^l` and `N - 2^l`, `0 ≤ l < m`, lie in `{1,…,N-1}`
and every residue of the first kind is smaller than every residue of the second kind. -/
theorem order_bounds {m l l' : ℕ} (hl : l < m) (hl' : l' < m) :
    1 ≤ 2 ^ l ∧ 2 ^ l < 2 ^ m + 1 ∧ (2 ^ m + 1) - 2 ^ l ≤ 2 ^ m ∧ 1 ≤ (2 ^ m + 1) - 2 ^ l ∧
      2 ^ l < (2 ^ m + 1) - 2 ^ l' := by
  have h1 : 0 < 2 ^ l := by positivity
  have h2 : 2 ^ l ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hl.le
  have h3 : 2 ^ l < 2 ^ m := by
    exact Nat.pow_lt_pow_right (by norm_num) hl
  have h4 : 2 ^ l' < 2 ^ m := by
    exact Nat.pow_lt_pow_right (by norm_num) hl'
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have e : 2 ^ (m' + 1) = 2 * 2 ^ m' := by ring
  have h5 : 2 ^ l ≤ 2 ^ m' := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h6 : 2 ^ l' ≤ 2 ^ m' := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨h1, by omega, by omega, by omega, by omega⟩

theorem order_inj1 {l l' : ℕ} (h : 2 ^ l = 2 ^ l') : l = l' :=
  Nat.pow_right_injective (le_refl 2) h

theorem order_inj2 {m l l' : ℕ} (hl : l < m) (hl' : l' < m)
    (h : (2 ^ m + 1) - 2 ^ l = (2 ^ m + 1) - 2 ^ l') : l = l' := by
  have h1 : 2 ^ l < 2 ^ m := by
    exact Nat.pow_lt_pow_right (by norm_num) hl
  have h2 : 2 ^ l' < 2 ^ m := by
    exact Nat.pow_lt_pow_right (by norm_num) hl'
  exact order_inj1 (by omega)

/-- Lemma `lem:order` (3). -/
theorem order_iff {m t e : ℕ} (hm : 1 ≤ m) (ht1 : 1 ≤ t) (ht2 : t ≤ 2 ^ m) :
    2 ^ e ≡ t [MOD 2 ^ m + 1] ↔
      ∃ l, l < m ∧ ((t = 2 ^ l ∧ e ≡ l [MOD 2 * m]) ∨
        (t = (2 ^ m + 1) - 2 ^ l ∧ e ≡ m + l [MOD 2 * m])) := by
  have hdec : e = 2 * m * (e / (2 * m)) + e % (2 * m) := (Nat.div_add_mod e (2 * m)).symm
  have hrlt : e % (2 * m) < 2 * m := Nat.mod_lt _ (by omega)
  have hp : 0 < 2 ^ m := by positivity
  constructor
  · intro h
    by_cases hr : e % (2 * m) < m
    · refine ⟨e % (2 * m), hr, Or.inl ⟨?_, ?_⟩⟩
      · have h1 : 2 ^ e ≡ 2 ^ (e % (2 * m)) [MOD 2 ^ m + 1] := by
          have := order_one (m := m) (q := e / (2 * m)) hr
          rw [← hdec] at this
          exact this
        have h2 := h1.symm.trans h
        have hb := order_bounds (m := m) (l := e % (2 * m)) (l' := e % (2 * m)) hr hr
        obtain ⟨b1, b2, b3, b4, b5⟩ := hb
        unfold Nat.ModEq at h2
        rw [Nat.mod_eq_of_lt b2, Nat.mod_eq_of_lt (by omega : t < 2 ^ m + 1)] at h2
        exact h2.symm
      · unfold Nat.ModEq
        exact (Nat.mod_mod e (2 * m)).symm
    · push Not at hr
      obtain ⟨l, hl⟩ : ∃ l, e % (2 * m) = m + l := ⟨e % (2 * m) - m, by omega⟩
      have hlm : l < m := by omega
      refine ⟨l, hlm, Or.inr ⟨?_, ?_⟩⟩
      · have h1 : 2 ^ e ≡ (2 ^ m + 1) - 2 ^ l [MOD 2 ^ m + 1] := by
          have := order_two (m := m) (q := e / (2 * m)) hlm
          have e2 : 2 * m * (e / (2 * m)) + m + l = e := by omega
          rw [e2] at this
          exact this
        have h2 := h1.symm.trans h
        have hb := order_bounds (m := m) (l := l) (l' := l) hlm hlm
        obtain ⟨b1, b2, b3, b4, b5⟩ := hb
        unfold Nat.ModEq at h2
        rw [Nat.mod_eq_of_lt (by omega : (2 ^ m + 1) - 2 ^ l < 2 ^ m + 1),
          Nat.mod_eq_of_lt (by omega : t < 2 ^ m + 1)] at h2
        exact h2.symm
      · unfold Nat.ModEq
        rw [hl, Nat.mod_eq_of_lt (by omega : m + l < 2 * m)]
  · rintro ⟨l, hl, (⟨rfl, h2⟩ | ⟨rfl, h2⟩)⟩
    · have hmod : e % (2 * m) = l := by
        unfold Nat.ModEq at h2
        rw [h2, Nat.mod_eq_of_lt (by omega : l < 2 * m)]
      have := order_one (m := m) (q := e / (2 * m)) hl
      rw [hmod] at hdec
      rw [← hdec] at this
      exact this
    · have hmod : e % (2 * m) = m + l := by
        unfold Nat.ModEq at h2
        rw [h2, Nat.mod_eq_of_lt (by omega : m + l < 2 * m)]
      have := order_two (m := m) (q := e / (2 * m)) hl
      have e2 : 2 * m * (e / (2 * m)) + m + l = e := by omega
      rw [e2] at this
      exact this

/-! ### Congruence helpers -/

/-- If `K (2^m + 1) = 2^{h+m} + c` then `2^h ≡ c (mod 2^m + 1)`. -/
theorem modeq_of_eq {K m h c : ℕ} (H : K * (2 ^ m + 1) = 2 ^ (h + m) + c) :
    2 ^ h ≡ c [MOD 2 ^ m + 1] := by
  have hA : 2 ^ (h + m) + c ≡ 0 [MOD 2 ^ m + 1] :=
    (Nat.modEq_zero_iff_dvd).2 ⟨K, by rw [← H]; ring⟩
  have hB : 2 ^ (h + m) + 2 ^ h ≡ 0 [MOD 2 ^ m + 1] :=
    (Nat.modEq_zero_iff_dvd).2 ⟨2 ^ h, by rw [pow_add]; ring⟩
  exact (Nat.ModEq.add_left_cancel' (2 ^ (h + m)) (hA.trans hB.symm)).symm

/-- If `2^h ≡ c (mod 2^m + 1)` then `2^m + 1` divides `2^{h+m} + c`. -/
theorem dvd_of_modeq {m h c : ℕ} (hmod : 2 ^ h ≡ c [MOD 2 ^ m + 1]) :
    (2 ^ m + 1) ∣ 2 ^ (h + m) + c := by
  have h1 : 2 ^ (h + m) + 2 ^ h ≡ 2 ^ (h + m) + c [MOD 2 ^ m + 1] :=
    Nat.ModEq.add_left _ hmod
  have h2 : 2 ^ (h + m) + 2 ^ h ≡ 0 [MOD 2 ^ m + 1] :=
    (Nat.modEq_zero_iff_dvd).2 ⟨2 ^ h, by rw [pow_add]; ring⟩
  exact (Nat.modEq_zero_iff_dvd).1 (h1.symm.trans h2)

/-- `2^h = K + w`: the equation `2^s w + c = K` is equivalent to `K (2^s + 1) = 2^{h+s} + c`. -/
theorem arith_eq {K w h s c : ℕ} (hw : 2 ^ h = K + w) :
    2 ^ s * w + c = K ↔ K * (2 ^ s + 1) = 2 ^ (h + s) + c := by
  have e : 2 ^ (h + s) = (K + w) * 2 ^ s := by rw [pow_add, hw]
  rw [e]
  constructor <;> intro H <;> nlinarith [H]

theorem le_two_pow_pred {s : ℕ} (hs : 1 ≤ s) : s ≤ 2 ^ (s - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
  have e : j + 1 - 1 = j := by omega
  rw [e]
  have := nat_lt_two_pow j
  omega

theorem pow_big : ∀ j : ℕ, j + 3 < 2 ^ (j + 2) := by
  intro j
  induction j with
  | zero => norm_num
  | succ j ih =>
    have e : 2 ^ (j + 1 + 2) = 2 * 2 ^ (j + 2) := by ring
    omega

/-! ### Failing states -/

/-- A failing state is not successful (Theorem `thm:step` (2a)), in the form used in
Section `sec:nonmembers`. -/
theorem not_succ_of_fail {J w t : ℕ} (hst : IsState J w) (hw : 1 ≤ w) (ht : 1 ≤ t)
    (h : 2 ^ t * w + (t + 1) = J + 1) : ¬ Succ J w := by
  have hS := least_three hst hw ht h
  obtain ⟨s, hs, hsJ⟩ := exists_S hst hw
  have hu := IsS_unique hS hs
  obtain ⟨m, hm⟩ : ∃ m, J = m + (t + 1) := ⟨J - (t + 1), by omega⟩
  subst hm
  exact (step_main hst hw hS (by omega)).1 h

/-! ### Theorem `thm:nonmembers` -/

/-- Theorem `thm:nonmembers`, with `s = m + 1`: if `m ≥ 1`, `m + 1 < 2^h` and
`2^h ≡ m + 1 (mod 2^m + 1)`, then `K = (2^{h+m} + m + 1)/(2^m + 1)` is an integer with
`2^{h-1} < K < 2^h` and `K + h - 3 ∉ 𝓐`. -/
theorem nonmembers_core {m h : ℕ} (hm : 1 ≤ m) (hsh : m + 1 < 2 ^ h)
    (hmod : 2 ^ h ≡ m + 1 [MOD 2 ^ m + 1]) :
    ∃ K, K * (2 ^ m + 1) = 2 ^ (h + m) + (m + 1) ∧ 2 ^ h < 2 * K ∧ K < 2 ^ h ∧
      hfun K = h ∧ ¬ Amem (K + h - 3) := by
  obtain ⟨K, hK⟩ := dvd_of_modeq hmod
  have hK' : K * (2 ^ m + 1) = 2 ^ (h + m) + (m + 1) := by rw [mul_comm]; exact hK.symm
  have hpow : 2 ^ (h + m) = 2 ^ h * 2 ^ m := pow_add 2 h m
  have hQ2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hPQ : 2 ^ h * 2 ≤ 2 ^ h * 2 ^ m := Nat.mul_le_mul_left _ hQ2
  rw [hpow] at hK'
  have hlt : K < 2 ^ h := by
    by_contra hc
    push Not at hc
    have h1 : 2 ^ h * (2 ^ m + 1) ≤ K * (2 ^ m + 1) := Nat.mul_le_mul_right _ hc
    nlinarith [h1, hK', hsh]
  have hlt2 : 2 ^ h < 2 * K := by
    by_contra hc
    push Not at hc
    have h1 : 2 * K * (2 ^ m + 1) ≤ 2 ^ h * (2 ^ m + 1) := Nat.mul_le_mul_right _ hc
    nlinarith [h1, hK', hPQ, hsh]
  have hK2 : 2 ≤ K := by omega
  have hfK : hfun K = h := hfun_of_bounds hK2 hlt.le hlt2
  refine ⟨K, by rw [hpow]; exact hK', hlt2, hlt, hfK, ?_⟩
  have hh1 : 1 ≤ h := by
    obtain ⟨a1, _, _⟩ := hfun_spec hK2
    omega
  obtain ⟨J, rfl⟩ : ∃ J, K = J + 1 := ⟨K - 1, by omega⟩
  have hJ : 1 ≤ J := by omega
  obtain ⟨w, hw⟩ : ∃ w, 2 ^ h = (J + 1) + w := ⟨2 ^ h - (J + 1), by omega⟩
  have hw1 : 1 ≤ w := by omega
  have hKeq : J + 1 = 2 ^ m * w + (m + 1) := by
    rw [hw] at hK'
    nlinarith [hK']
  have hwQ : 2 * w ≤ 2 ^ m * w := Nat.mul_le_mul_right w hQ2
  have hst : IsState J w := ⟨hJ, by omega⟩
  have hnot : ¬ Succ J w := not_succ_of_fail hst hw1 hm (by omega)
  have hb : beta (J + 1) = (J + 1 + h - 3) + 3 := by
    unfold beta
    rw [hfK]
    omega
  rw [amem_iff_state hJ hb, hfK]
  intro hin
  apply hnot
  have e : 2 ^ h - (J + 1) = w := by omega
  rw [e] at hin
  exact hin

/-- Theorem `thm:nonmembers` (1) (the congruence): `s = 2^i`, `m = s - 1`, `h > i`,
`h ≡ i (mod 2m)` give `2^h ≡ s (mod 2^m + 1)`. -/
theorem nonmem_family_one {i m h : ℕ} (hm : 2 ^ i = m + 1) (hih : i < h)
    (hmod : h ≡ i [MOD 2 * m]) : 2 ^ h ≡ m + 1 [MOD 2 ^ m + 1] := by
  obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd' hih.le).1 hmod.symm
  have hh : h = i + 2 * m * q := by omega
  have h1 := (pow_period m q).mul_left (2 ^ i)
  rw [mul_one, ← pow_add, hm] at h1
  rw [hh]
  exact h1

/-- Theorem `thm:nonmembers` (2) (the congruence): `s = 3`, `h ≡ 3 (mod 4)`. -/
theorem nonmem_family_two {h : ℕ} (hmod : h ≡ 3 [MOD 4]) : 2 ^ h ≡ 3 [MOD 2 ^ 2 + 1] := by
  unfold Nat.ModEq at hmod
  have hh : h = 2 * 2 * (h / 4) + 3 := by omega
  have h1 := (pow_period 2 (h / 4)).mul_right (2 ^ 3)
  rw [one_mul, ← pow_add] at h1
  have h2 : 2 ^ 3 ≡ 3 [MOD 2 ^ 2 + 1] := by
    decide
  rw [hh]
  exact h1.trans h2

/-! ### Theorem `thm:firststep` -/

theorem run_zero {J w : ℕ} {T : Finset ℕ} (h : Run 0 J w T) : w = 0 ∧ T = ∅ ∧ 1 ≤ J := by
  cases h with
  | done hJ => exact ⟨rfl, rfl, hJ⟩

theorem run_succ_inv {n J w : ℕ} {T : Finset ℕ} (h : Run (n + 1) J w T) :
    ∃ m t w' T', J = m + (t + 1) ∧ 1 ≤ w ∧ IsS J w (t + 1) ∧ 1 ≤ m ∧
      2 ^ t * w + (t + 1) ≠ J + 1 ∧ 2 ^ (t + 1) * w = (m + 1) + w' ∧ Run n m w' T' := by
  cases h with
  | @step m t w w' n T hw hS hm hnf heq h =>
    exact ⟨m, t, w', T, rfl, hw, hS, hm, hnf, heq, h⟩

/-- Theorem `thm:firststep` (1): the loop is not entered iff `K = 2^h`. -/
theorem firststep_one {K : ℕ} (hK : 2 ≤ K) :
    (∃ T, Run 0 (K - 1) (2 ^ hfun K - K) T) ↔ K = 2 ^ hfun K := by
  have hge := hfun_ge K
  constructor
  · rintro ⟨T, hT⟩
    have := (run_zero hT).1
    omega
  · intro h
    have h0 : 2 ^ hfun K - K = 0 := by omega
    rw [h0]
    exact ⟨∅, Run.done (by omega)⟩

/-- One iteration: for a state `(J, w)` with `w ≥ 1`, the algorithm succeeds after exactly one
iteration iff `2^{t+1} w + (t+1) = J + 1` for some `t` (equation `eq:onestep`). -/
theorem onestep_iff {J w : ℕ} (hst : IsState J w) (hw : 1 ≤ w) :
    (∃ T, Run 1 J w T) ↔ ∃ t, 2 ^ (t + 1) * w + (t + 1) = J + 1 := by
  constructor
  · rintro ⟨T, hT⟩
    obtain ⟨m, t, w', T', hJ, _, _, _, _, heq, hrun⟩ := run_succ_inv (n := 0) hT
    have := (run_zero hrun).1
    refine ⟨t, ?_⟩
    omega
  · rintro ⟨t, ht⟩
    obtain ⟨hS, hnf⟩ := least_two hst hw ht
    have hp : 2 ≤ 2 ^ (t + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (t + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpw : 2 * 1 ≤ 2 ^ (t + 1) * w := Nat.mul_le_mul hp hw
    obtain ⟨m, hm⟩ : ∃ m, J = m + (t + 1) := ⟨J - (t + 1), by omega⟩
    have hm1 : 1 ≤ m := by omega
    subst hm
    exact ⟨_, Run.step hw hS hm1 hnf (by omega) (Run.done hm1)⟩

/-- Theorem `thm:firststep` (2). -/
theorem firststep_two {K : ℕ} (hK : 2 ≤ K) :
    (∃ T, Run 1 (K - 1) (2 ^ hfun K - K) T) ↔
      ∃ k, k + 2 ≤ hfun K ∧ hfun K ≡ k [MOD 2 ^ (k + 1)] ∧
        K * (2 ^ (2 ^ k) + 1) = 2 ^ (hfun K + 2 ^ k) + 2 ^ k := by
  have hge := hfun_ge K
  obtain ⟨hh1, hh2, hh3⟩ := hfun_spec hK
  obtain ⟨hS1, hS2⟩ := leading_state hK
  obtain ⟨w, hw⟩ : ∃ w, 2 ^ hfun K = K + w := ⟨2 ^ hfun K - K, by omega⟩
  have hwv : 2 ^ hfun K - K = w := by omega
  rw [hwv]
  constructor
  · intro hrun
    have hw1 : 1 ≤ w := by
      obtain ⟨T, hT⟩ := hrun
      obtain ⟨m, t, w', T', _, h1, _⟩ := run_succ_inv (n := 0) hT
      exact h1
    have hst : IsState (K - 1) w := ⟨by omega, by omega⟩
    obtain ⟨t, ht⟩ := (onestep_iff hst hw1).1 hrun
    have ht' : 2 ^ (t + 1) * w + (t + 1) = K := by omega
    have heq := (arith_eq (s := t + 1) (c := t + 1) hw).1 ht'
    have hmod := modeq_of_eq heq
    have hs1 : 1 ≤ t + 1 := by omega
    have hs2 : t + 1 ≤ 2 ^ (t + 1) := (nat_lt_two_pow (t + 1)).le
    obtain ⟨l, hl, hcase⟩ := (order_iff (m := t + 1) (t := t + 1) (e := hfun K) hs1 hs1 hs2).1
      hmod
    rcases hcase with ⟨hl1, hl2⟩ | ⟨hl1, hl2⟩
    · -- s = 2^l
      have hlt : t + 1 < 2 ^ hfun K := by
        have h1 : (K + 1) * (2 ^ (t + 1) + 1) ≤ 2 ^ hfun K * (2 ^ (t + 1) + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        have h3 : 2 ^ hfun K * (2 ^ (t + 1) + 1) = 2 ^ (hfun K + (t + 1)) + 2 ^ hfun K := by
          rw [pow_add]; ring
        nlinarith [h1, h3, heq]
      have hlh : l < hfun K := by
        by_contra hc
        push Not at hc
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hc
        omega
      have hd := (Nat.modEq_iff_dvd' hlh.le).1 hl2.symm
      have hpos : 0 < hfun K - l := by omega
      have hle := Nat.le_of_dvd hpos hd
      refine ⟨l, by omega, ?_, ?_⟩
      · have e : 2 ^ (l + 1) = 2 * (t + 1) := by rw [hl1]; ring
        rw [e]
        exact hl2
      · rw [← hl1]
        exact heq
    · exfalso
      have hpl : t + 1 ≤ 2 ^ t := by
        have := le_two_pow_pred (s := t + 1) (by omega)
        simpa using this
      have hle : 2 ^ l ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
      have e : 2 ^ (t + 1) = 2 * 2 ^ t := by ring
      omega
  · rintro ⟨k, hk2, hkmod, heq⟩
    have hKlt : K < 2 ^ hfun K := by
      by_contra hc
      have hKe : K = 2 ^ hfun K := by omega
      have h3 : 2 ^ hfun K * (2 ^ (2 ^ k) + 1) = 2 ^ (hfun K + 2 ^ k) + 2 ^ hfun K := by
        rw [pow_add]; ring
      have h4 : K * (2 ^ (2 ^ k) + 1) = 2 ^ hfun K * (2 ^ (2 ^ k) + 1) := by
        rw [← hKe]
      have h5 : 2 ^ hfun K = 2 ^ k := by omega
      have h6 : hfun K = k := order_inj1 h5
      omega
    have hw1 : 1 ≤ w := by omega
    have hst : IsState (K - 1) w := ⟨by omega, by omega⟩
    refine (onestep_iff hst hw1).2 ?_
    have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    obtain ⟨t, ht⟩ : ∃ t, 2 ^ k = t + 1 := ⟨2 ^ k - 1, by omega⟩
    refine ⟨t, ?_⟩
    rw [ht] at heq
    have := (arith_eq (s := t + 1) (c := t + 1) hw).2 heq
    omega

/-- Theorem `thm:firststep` (3): the algorithm fails at its first iteration iff
`K (2^{s-1} + 1) = 2^{h+s-1} + s` with `s = 2^i`, `i ≥ 1`, `h > i`, `h ≡ i (mod 2(2^i - 1))`,
or `s = 3` and `h ≡ 3 (mod 4)` (Theorem `thm:nonmembers` (1), (2)); here `s - 1 = 2^i - 1`. -/
theorem firststep_three {K : ℕ} (hK : 2 ≤ K) (hlt : K < 2 ^ hfun K) :
    Fails (K - 1) (2 ^ hfun K - K) ↔
      (∃ i, 1 ≤ i ∧ i < hfun K ∧ hfun K ≡ i [MOD 2 * (2 ^ i - 1)] ∧
        K * (2 ^ (2 ^ i - 1) + 1) = 2 ^ (hfun K + (2 ^ i - 1)) + 2 ^ i) ∨
      (hfun K ≡ 3 [MOD 4] ∧ K * (2 ^ 2 + 1) = 2 ^ (hfun K + 2) + 3) := by
  have hge := hfun_ge K
  obtain ⟨hh1, hh2, hh3⟩ := hfun_spec hK
  obtain ⟨hS1, hS2⟩ := leading_state hK
  obtain ⟨w, hw⟩ : ∃ w, 2 ^ hfun K = K + w := ⟨2 ^ hfun K - K, by omega⟩
  have hwv : 2 ^ hfun K - K = w := by omega
  have hw1 : 1 ≤ w := by omega
  have hst : IsState (K - 1) w := ⟨by omega, by omega⟩
  rw [hwv]
  rw [fails_iff hst hw1]
  constructor
  · rintro ⟨t, ht1, ht⟩
    have ht' : 2 ^ t * w + (t + 1) = K := by omega
    have heq := (arith_eq (s := t) (c := t + 1) hw).1 ht'
    have hmod := modeq_of_eq heq
    have hs2 : t + 1 ≤ 2 ^ t := by
      have := le_two_pow_pred (s := t + 1) (by omega)
      simpa using this
    obtain ⟨l, hl, hcase⟩ := (order_iff (m := t) (t := t + 1) (e := hfun K) ht1 (by omega) hs2).1
      hmod
    have hbig : t + 1 < 2 ^ hfun K := by
      have h1 : (K + 1) * (2 ^ t + 1) ≤ 2 ^ hfun K * (2 ^ t + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      have h3 : 2 ^ hfun K * (2 ^ t + 1) = 2 ^ (hfun K + t) + 2 ^ hfun K := by
        rw [pow_add]; ring
      nlinarith [h1, h3, heq]
    rcases hcase with ⟨hl1, hl2⟩ | ⟨hl1, hl2⟩
    · left
      have e : 2 ^ l - 1 = t := by omega
      refine ⟨l, ?_, ?_, ?_, ?_⟩
      · by_contra hc
        have h0 : l = 0 := by omega
        subst h0
        omega
      · have hlt' : 2 ^ l < 2 ^ hfun K := by rw [← hl1]; exact hbig
        by_contra hc
        push Not at hc
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hc
        omega
      · rw [e]
        exact hl2
      · rw [e, ← hl1]
        exact heq
    · -- second alternative: only `t = 1` or `t = 2` are possible
      have hle : 2 ^ l ≤ 2 ^ (t - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have ht3 : t ≤ 2 := by
        by_contra hc
        obtain ⟨j, hj⟩ : ∃ j, t = j + 3 := ⟨t - 3, by omega⟩
        subst hj
        have h1 := pow_big j
        have e1 : 2 ^ (j + 3) = 2 * 2 ^ (j + 2) := by ring
        have e2 : j + 3 - 1 = j + 2 := by omega
        rw [e2] at hle
        omega
      rcases (by omega : t = 1 ∨ t = 2) with rfl | rfl
      · left
        interval_cases l
        refine ⟨1, le_refl _, ?_, ?_, ?_⟩
        · by_contra hc
          push Not at hc
          have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hc
          omega
        · have e3 : 2 * (2 ^ 1 - 1) = 2 * 1 := by norm_num
          rw [e3]
          simpa using hl2
        · have e1 : (2 : ℕ) ^ 1 - 1 = 1 := by norm_num
          rw [e1]
          omega
      · right
        interval_cases l
        · exfalso
          omega
        · refine ⟨?_, ?_⟩
          · exact hl2
          · omega
  · rintro (⟨i, hi1, hih, hmod, heq⟩ | ⟨hmod, heq⟩)
    · obtain ⟨t, ht⟩ : ∃ t, 2 ^ i - 1 = t := ⟨_, rfl⟩
      have hp : 2 ≤ 2 ^ i := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi1
      refine ⟨t, by omega, ?_⟩
      rw [ht] at heq
      have h2i : 2 ^ i = t + 1 := by omega
      rw [h2i] at heq
      have := (arith_eq (s := t) (c := t + 1) hw).2 heq
      omega
    · refine ⟨2, by norm_num, ?_⟩
      have := (arith_eq (s := 2) (c := 3) hw).2 heq
      omega

/-! ### Proposition `prop:nicolasfamilies` -/

/-- Proposition `prop:nicolasfamilies` (1). -/
theorem nicolas_one (a : ℕ) :
    (¬ ∃ K, 2 ≤ K ∧ beta K = a + 3) ↔ ∃ r, 1 ≤ r ∧ a + 2 = 2 ^ r + r := by
  have hb : 3 ≤ a + 3 := by omega
  rw [beta_range hb]
  push Not
  constructor
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, by omega⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, by omega⟩

theorem two_pow_mod_three_odd {a : ℕ} (h : a % 2 = 1) : 2 ^ a % 3 = 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, a = 2 * j + 1 := ⟨a / 2, by omega⟩
  have h4 : 4 ^ j % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have e : 2 ^ (2 * j + 1) = 4 ^ j * 2 := by
    rw [pow_succ, pow_mul]
    norm_num
  rw [e]
  omega

theorem two_pow_mod_three_even {a : ℕ} (h : a % 2 = 0) : 2 ^ a % 3 = 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, a = 2 * j := ⟨a / 2, by omega⟩
  have h4 : 4 ^ j % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have e : 2 ^ (2 * j) = 4 ^ j := by
    rw [pow_mul]
    norm_num
  rw [e]
  exact h4

/-- Proposition `prop:nicolasfamilies` (2), first direction: for odd `a ≥ 3` put `h = a - 1`,
`K = (2^a + 1)/3`; then `h ≥ 2` is even, `K (2^1 + 1) = 2^{h+1} + 1` and
`3 (K + h - 3) + 11 = 3a + 2^a`, i.e. `K + h - 3 = a + (2^a - 11)/3`. -/
theorem nicolas_two_fwd {a : ℕ} (ha : 3 ≤ a) (hodd : a % 2 = 1) :
    ∃ K h, h + 1 = a ∧ 2 ≤ h ∧ h % 2 = 0 ∧ 3 * K = 2 ^ a + 1 ∧
      K * (2 ^ 1 + 1) = 2 ^ (h + 1) + 1 ∧ 3 * (K + h - 3) + 11 = 3 * a + 2 ^ a := by
  have hm := two_pow_mod_three_odd hodd
  have h8 : 8 ≤ 2 ^ a := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  refine ⟨(2 ^ a + 1) / 3, a - 1, by omega, by omega, by omega, by omega, ?_, ?_⟩
  · have e : a - 1 + 1 = a := by omega
    have e2 : (2 : ℕ) ^ 1 + 1 = 3 := by norm_num
    rw [e, e2]
    omega
  · omega

/-- Proposition `prop:nicolasfamilies` (2), second direction. -/
theorem nicolas_two_bwd {K h : ℕ} (h2 : 2 ≤ h) (hev : h % 2 = 0)
    (hK : K * (2 ^ 1 + 1) = 2 ^ (h + 1) + 1) :
    3 ≤ h + 1 ∧ (h + 1) % 2 = 1 ∧ 3 * (K + h - 3) + 11 = 3 * (h + 1) + 2 ^ (h + 1) := by
  have h8 : 8 ≤ 2 ^ (h + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (h + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e2 : (2 : ℕ) ^ 1 + 1 = 3 := by norm_num
  rw [e2] at hK
  refine ⟨by omega, by omega, ?_⟩
  omega

/-- Proposition `prop:nicolasfamilies` (3), first direction: for even `a ≥ 4` put `h = a - 1`,
`K = (2^a + 2)/3`; then `h ≥ 3` is odd, `K (2^{2^1 - 1} + 1) = 2^{h + 2^1 - 1} + 2^1` and
`3 (K + h - 3) + 10 = 3a + 2^a`, i.e. `K + h - 3 = a + (2^a - 10)/3`. -/
theorem nicolas_three_fwd {a : ℕ} (ha : 4 ≤ a) (hev : a % 2 = 0) :
    ∃ K h, h + 1 = a ∧ 3 ≤ h ∧ h % 2 = 1 ∧ 3 * K = 2 ^ a + 2 ∧
      K * (2 ^ (2 ^ 1 - 1) + 1) = 2 ^ (h + (2 ^ 1 - 1)) + 2 ^ 1 ∧
      3 * (K + h - 3) + 10 = 3 * a + 2 ^ a := by
  have hm := two_pow_mod_three_even hev
  have h8 : 16 ≤ 2 ^ a := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  refine ⟨(2 ^ a + 2) / 3, a - 1, by omega, by omega, by omega, by omega, ?_, ?_⟩
  · have e : a - 1 + (2 ^ 1 - 1) = a := by omega
    have e2 : (2 : ℕ) ^ (2 ^ 1 - 1) + 1 = 3 := by norm_num
    rw [e, e2]
    omega
  · omega

/-- Proposition `prop:nicolasfamilies` (3), second direction. -/
theorem nicolas_three_bwd {K h : ℕ} (h3 : 3 ≤ h) (hodd : h % 2 = 1)
    (hK : K * (2 ^ (2 ^ 1 - 1) + 1) = 2 ^ (h + (2 ^ 1 - 1)) + 2 ^ 1) :
    4 ≤ h + 1 ∧ (h + 1) % 2 = 0 ∧ 3 * (K + h - 3) + 10 = 3 * (h + 1) + 2 ^ (h + 1) := by
  have h8 : 16 ≤ 2 ^ (h + 1) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (h + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e1 : (2 : ℕ) ^ 1 - 1 = 1 := by norm_num
  have e2 : (2 : ℕ) ^ 1 + 1 = 3 := by norm_num
  rw [e1] at hK
  rw [e2] at hK
  refine ⟨by omega, by omega, ?_⟩
  omega

end SequenceNicolas.Families
