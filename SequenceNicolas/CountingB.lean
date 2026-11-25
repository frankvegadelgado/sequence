module

public import Mathlib
public import SequenceNicolas.CountBase
public import SequenceNicolas.Counting
public import SequenceNicolas.CountingA

@[expose] public section

/-!
# Theorem `thm:counting`, the bound for `B(x)`

The non-members of Theorem `thm:nonmembers`: for `m ≥ 1` and `h` with `2^h ≡ m + 1 (mod 2^m + 1)`
the candidate `K = (2^{h+m} + m + 1)/(2^m + 1)` has `h(K) = h` and `K + h - 3 ∉ 𝓐`.
-/

namespace SequenceNicolas.Counting

open SequenceNicolas.CountBase SequenceNicolas.Recursion SequenceNicolas.Families

open scoped Classical

/-- The candidate of the non-member families. -/
def Kq (m h : ℕ) : ℕ := (2 ^ (h + m) + (m + 1)) / (2 ^ m + 1)

/-- Hypotheses of `nonmembers_core`. -/
abbrev Good (m h : ℕ) : Prop := 1 ≤ m ∧ m + 1 < 2 ^ h ∧ 2 ^ h ≡ m + 1 [MOD 2 ^ m + 1]

theorem Kq_spec {m h : ℕ} (hg : Good m h) :
    Kq m h * (2 ^ m + 1) = 2 ^ (h + m) + (m + 1) ∧ 2 ^ h < 2 * Kq m h ∧ Kq m h < 2 ^ h ∧
    2 ≤ Kq m h ∧ hfun (Kq m h) = h ∧ ¬ Amem (Kq m h + h - 3) := by
  obtain ⟨h1, h2, h3⟩ := hg
  obtain ⟨K, hK1, hK2, hK3, hK4, hK5⟩ := nonmembers_core h1 h2 h3
  have hdiv : Kq m h = K := by
    unfold Kq
    exact Nat.div_eq_of_eq_mul_left (by positivity) hK1.symm
  rw [hdiv]
  exact ⟨hK1, hK2, hK3, by omega, hK4, hK5⟩

theorem Kq_inj {m h m' h' : ℕ} (hg : Good m h) (hg' : Good m' h')
    (heq : Kq m h = Kq m' h') : m = m' ∧ h = h' := by
  obtain ⟨e1, l1, r1, k1, f1, _⟩ := Kq_spec hg
  obtain ⟨e2, l2, r2, k2, f2, _⟩ := Kq_spec hg'
  have hh : h = h' := by
    rw [heq] at f1
    omega
  subst hh
  rw [← heq] at e2
  refine ⟨?_, rfl⟩
  have hm : m = m' := by
    exact eqn_inj (m := m) (m' := m') (e := m + 1) (e' := m' + 1) (h := h) (K := Kq m h)
      (by intro hlt; omega) (by intro hlt; omega) e1 e2 r1
  exact hm

theorem Kq_mem {H m h : ℕ} (hg : Good m h) (hh : h ≤ H) : Kq m h ∈ KB H := by
  obtain ⟨e1, l1, r1, k1, f1, hA⟩ := Kq_spec hg
  rw [mem_KB]
  refine ⟨k1, by omega, ?_⟩
  rw [f1]
  exact hA

/-! ### The family (1) of Theorem `thm:nonmembers` -/

theorem good_one {i t : ℕ} (hi : 1 ≤ i) (ht : 1 ≤ t) :
    Good (2 ^ i - 1) (i + 2 * (2 ^ i - 1) * t) := by
  have h2 : 2 ≤ 2 ^ i := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
  have hm : 1 ≤ 2 ^ i - 1 := by omega
  have hp : 1 * 1 ≤ (2 ^ i - 1) * t := Nat.mul_le_mul hm ht
  have hmul : 2 * (2 ^ i - 1) * t = 2 * ((2 ^ i - 1) * t) := by ring
  have hih : i < i + 2 * (2 ^ i - 1) * t := by omega
  have hpow : 2 ^ i < 2 ^ (i + 2 * (2 ^ i - 1) * t) := by
    exact Nat.pow_lt_pow_right (by norm_num) hih
  refine ⟨hm, by omega, ?_⟩
  have := nonmem_family_one (i := i) (m := 2 ^ i - 1) (h := i + 2 * (2 ^ i - 1) * t)
    (by omega) hih (by
      show (i + 2 * (2 ^ i - 1) * t) % (2 * (2 ^ i - 1)) = i % (2 * (2 ^ i - 1))
      exact Nat.add_mul_mod_self_left i (2 * (2 ^ i - 1)) t)
  exact this

/-- The index set `1 ≤ i = j + 1 ≤ κ`, `1 ≤ t ≤ ⌊(H - i)/(2(2^i - 1))⌋`. -/
noncomputable def idxN (H κ : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.range κ).sigma (fun j => Finset.Icc 1 ((H - (j + 1)) / (2 * (2 ^ (j + 1) - 1))))

theorem card_idxN (H κ : ℕ) :
    (idxN H κ).card = ∑ j ∈ Finset.range κ, (H - (j + 1)) / (2 * (2 ^ (j + 1) - 1)) := by
  unfold idxN
  rw [Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.card_Icc]
  exact Nat.add_sub_cancel _ _

theorem idxN_mem {H κ j t : ℕ} (hκ : κ ≤ H) (hp : (⟨j, t⟩ : Σ _ : ℕ, ℕ) ∈ idxN H κ) :
    1 ≤ t ∧ j + 1 + 2 * (2 ^ (j + 1) - 1) * t ≤ H := by
  unfold idxN at hp
  simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hp
  obtain ⟨hj, ht1, ht2⟩ := hp
  have h2 : 2 ≤ 2 ^ (j + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpos : 0 < 2 * (2 ^ (j + 1) - 1) := by omega
  have h1 : t * (2 * (2 ^ (j + 1) - 1)) ≤ H - (j + 1) := (Nat.le_div_iff_mul_le hpos).1 ht2
  have h3 : 2 * (2 ^ (j + 1) - 1) * t = t * (2 * (2 ^ (j + 1) - 1)) := Nat.mul_comm _ _
  refine ⟨ht1, ?_⟩
  omega

/-- The map of the index set into the candidates. -/
noncomputable def fN (p : Σ _ : ℕ, ℕ) : ℕ :=
  Kq (2 ^ (p.1 + 1) - 1) ((p.1 + 1) + 2 * (2 ^ (p.1 + 1) - 1) * p.2)

theorem two_pow_sub_inj {j j' : ℕ} (h : 2 ^ (j + 1) - 1 = 2 ^ (j' + 1) - 1) : j = j' := by
  have a : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
  have b : 1 ≤ 2 ^ (j' + 1) := Nat.one_le_two_pow
  have hp : 2 ^ (j + 1) = 2 ^ (j' + 1) := by omega
  have := Nat.pow_right_injective (le_refl 2) hp
  omega

theorem two_pow_ne_three {j : ℕ} : 2 ^ (j + 1) - 1 ≠ 2 := by
  have : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  omega

/-! ### The family (2): `h ≡ 3 (mod 4)` -/

theorem good_two {h : ℕ} (hh : 3 ≤ h) (hmod : h ≡ 3 [MOD 4]) : Good 2 h := by
  have h8 : 2 ^ 3 ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
  refine ⟨by norm_num, by omega, ?_⟩
  have := nonmem_family_two hmod
  exact this

/-- `h = 3 + 4 u`, `0 ≤ u ≤ (H - 3)/4`. -/
noncomputable def f2 (u : ℕ) : ℕ := Kq 2 (3 + 4 * u)

theorem Kq_sep {m h : ℕ} (hg : Good m h) : 2 * 2 ^ h < 3 * Kq m h := by
  obtain ⟨e1, _⟩ := Kq_spec hg
  obtain ⟨h1, _⟩ := hg
  have hQ : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h1
  have e2 : 2 ^ (h + m) = 2 ^ h * 2 ^ m := pow_add _ _ _
  rw [e2] at e1
  exact sep_gen hQ (by omega) e1

/-- The non-members of Theorem `thm:nonmembers`: families (1) and (2). -/
noncomputable def Nset (H κ : ℕ) : Finset ℕ :=
  (idxN H κ).image fN ∪ (Finset.range ((H - 3) / 4 + 1)).image f2

theorem good_two' {u : ℕ} : Good 2 (3 + 4 * u) :=
  good_two (by omega) (by
    show (3 + 4 * u) % 4 = 3 % 4
    omega)

theorem Nset_prop {H κ x : ℕ} (hH : 3 ≤ H) (hκ : κ ≤ H) (hx : x ∈ Nset H κ) :
    x ∈ KB H ∧ 2 * 2 ^ hfun x < 3 * x := by
  unfold Nset at hx
  rcases Finset.mem_union.1 hx with hx | hx
  · obtain ⟨⟨j, t⟩, hp, rfl⟩ := Finset.mem_image.1 hx
    have a := idxN_mem hκ hp
    have g := good_one (i := j + 1) (by omega) a.1
    refine ⟨Kq_mem g a.2, ?_⟩
    obtain ⟨_, _, _, _, f1, _⟩ := Kq_spec g
    rw [show fN ⟨j, t⟩ = Kq (2 ^ (j + 1) - 1) ((j + 1) + 2 * (2 ^ (j + 1) - 1) * t) from rfl, f1]
    exact Kq_sep g
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
    have hu' := Finset.mem_range.1 hu
    have g : Good 2 (3 + 4 * u) := good_two'
    refine ⟨Kq_mem g (by omega), ?_⟩
    obtain ⟨_, _, _, _, f1, _⟩ := Kq_spec g
    show 2 * 2 ^ hfun (Kq 2 (3 + 4 * u)) < 3 * Kq 2 (3 + 4 * u)
    rw [f1]
    exact Kq_sep g

theorem Nset_card {H κ : ℕ} (_hH : 3 ≤ H) (hκ : κ ≤ H) :
    (Nset H κ).card = (∑ j ∈ Finset.range κ, (H - (j + 1)) / (2 * (2 ^ (j + 1) - 1)))
      + ((H - 3) / 4 + 1) := by
  have hS1 : ((idxN H κ).image fN).card = (idxN H κ).card := by
    apply Finset.card_image_of_injOn
    rintro ⟨j, t⟩ hp ⟨j', t'⟩ hp' heq
    have a := idxN_mem hκ hp
    have b := idxN_mem hκ hp'
    have g1 := good_one (i := j + 1) (by omega) a.1
    have g2 := good_one (i := j' + 1) (by omega) b.1
    obtain ⟨hm, hh⟩ := Kq_inj g1 g2 heq
    have hj : j = j' := two_pow_sub_inj hm
    subst hj
    have hpos : 0 < 2 * (2 ^ (j + 1) - 1) := by
      have : 2 ≤ 2 ^ (j + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have ht : t = t' := by
      have : 2 * (2 ^ (j + 1) - 1) * t = 2 * (2 ^ (j + 1) - 1) * t' := by omega
      exact Nat.eq_of_mul_eq_mul_left hpos this
    subst ht
    rfl
  have hS2 : ((Finset.range ((H - 3) / 4 + 1)).image f2).card = (H - 3) / 4 + 1 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro u _ u' _ heq
    obtain ⟨_, hh⟩ := Kq_inj (good_two' (u := u)) (good_two' (u := u')) heq
    omega
  have hdisj : Disjoint ((idxN H κ).image fN) ((Finset.range ((H - 3) / 4 + 1)).image f2) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨⟨j, t⟩, hp, rfl⟩ := Finset.mem_image.1 hx1
    obtain ⟨u, hu, hux⟩ := Finset.mem_image.1 hx2
    have a := idxN_mem hκ hp
    have g1 := good_one (i := j + 1) (by omega) a.1
    have hux' : Kq 2 (3 + 4 * u) = fN ⟨j, t⟩ := hux
    obtain ⟨hm, _⟩ := Kq_inj (good_two' (u := u)) g1 hux'
    exact two_pow_ne_three hm.symm
  unfold Nset
  rw [card_union_disj hdisj, hS1, hS2, card_idxN]

theorem B_nat {n H κ : ℕ} (hn : 2 ^ (H + 1) ≤ n) (hH : 3 ≤ H) (hκ : κ ≤ H) :
    H + ∑ j ∈ Finset.range κ, (H - (j + 1)) / (2 * (2 ^ (j + 1) - 1)) + ((H - 3) / 4 + 1)
      ≤ Bcount n := by
  have hsub : Nset H κ ⊆ KB H := fun x hx => (Nset_prop hH hκ hx).1
  have h1 := Finset.card_le_card hsub
  rw [Nset_card hH hκ] at h1
  have h2 := KB_le hn
  omega

/-! ### The real estimates -/

theorem n1_real {H κ : ℕ} (hκ : κ ≤ H) (hHκ : H < 2 ^ (κ + 1)) :
    Econst / 2 * (H : ℝ) - κ - 4 ≤
      ((∑ j ∈ Finset.range κ, (H - (j + 1)) / (2 * (2 ^ (j + 1) - 1)) : ℕ) : ℝ) := by
  have hterm : ∀ j ∈ Finset.range κ,
      (H : ℝ) / 2 * (1 / ((2 : ℝ) ^ (j + 1) - 1)) - ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ (j + 1) - 1
        ≤ (((H - (j + 1)) / (2 * (2 ^ (j + 1) - 1)) : ℕ) : ℝ) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have hx2 : (2 : ℝ) ≤ 2 ^ (j + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hxn : 2 ≤ 2 ^ (j + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hb : 0 < 2 * (2 ^ (j + 1) - 1) := by omega
    have h := nat_div_ge (H - (j + 1)) (2 * (2 ^ (j + 1) - 1)) hb
    have e1 : (((H - (j + 1) : ℕ)) : ℝ) = (H : ℝ) - ((j : ℝ) + 1) := by
      rw [Nat.cast_sub (show j + 1 ≤ H by omega)]
      push_cast; ring
    have e2 : (((2 * (2 ^ (j + 1) - 1) : ℕ)) : ℝ) = 2 * ((2 : ℝ) ^ (j + 1) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ 2 ^ (j + 1) by omega)]
      push_cast; ring
    rw [e1, e2] at h
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (2 : ℝ) ^ (j + 1) := ⟨_, rfl⟩
    rw [← hx] at h hx2
    have hxp : (1 / 2 : ℝ) ^ (j + 1) = 1 / x := by rw [hx, one_div_pow]
    rw [hxp, ← hx]
    have hx1 : x - 1 ≠ 0 := by intro h0; linarith
    have hxpos : 0 < x := by linarith
    have hkey : ((H : ℝ) - ((j : ℝ) + 1)) / (2 * (x - 1))
        = (H : ℝ) / 2 * (1 / (x - 1)) - ((j : ℝ) + 1) / (2 * (x - 1)) := by
      field_simp
    have hle : ((j : ℝ) + 1) / (2 * (x - 1)) ≤ ((j : ℝ) + 1) / x := by
      exact div_le_div_of_nonneg_left (by positivity) hxpos (by linarith)
    have hj1 : ((j : ℝ) + 1) * (1 / x) = ((j : ℝ) + 1) / x := by ring
    rw [hj1]
    linarith
  have hsum := Finset.sum_le_sum hterm
  have e : ∑ j ∈ Finset.range κ,
      ((H : ℝ) / 2 * (1 / ((2 : ℝ) ^ (j + 1) - 1)) - ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ (j + 1) - 1)
      = (H : ℝ) / 2 * ∑ j ∈ Finset.range κ, 1 / ((2 : ℝ) ^ (j + 1) - 1)
        - ∑ j ∈ Finset.range κ, ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ (j + 1) - κ := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
  rw [e] at hsum
  have hE := E_tail κ
  have hii := ii_sum_le κ
  have hq : (H : ℝ) * (1 / 2 : ℝ) ^ κ < 2 := by
    have h1 : (H : ℝ) < 2 ^ (κ + 1) := by exact_mod_cast hHκ
    have e' : (1 / 2 : ℝ) ^ κ = 2 / 2 ^ (κ + 1) := by
      rw [one_div_pow, pow_succ]
      field_simp
    rw [e', mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [h1]
  have hH0 : (0 : ℝ) ≤ (H : ℝ) / 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left (show Econst - 2 * (1 / 2 : ℝ) ^ κ ≤
      ∑ j ∈ Finset.range κ, 1 / ((2 : ℝ) ^ (j + 1) - 1) by linarith) hH0
  push_cast at hsum ⊢
  nlinarith [hsum, hm, hq, hii]

theorem n2_real {H : ℕ} (hH : 3 ≤ H) : (H : ℝ) / 4 - 1 ≤ (((H - 3) / 4 + 1 : ℕ) : ℝ) := by
  have h := nat_div_ge (H - 3) 4 (by norm_num)
  have e1 : (((H - 3 : ℕ)) : ℝ) = (H : ℝ) - 3 := by
    rw [Nat.cast_sub hH]
    norm_num
  rw [e1] at h
  push_cast at h ⊢
  linarith

/-- Theorem `thm:counting`, second bound: `B(n) ≥ (5/4 + E/2) H - log₂ H - 5`. -/
theorem counting_B {n H : ℕ} (hn : 2 ^ (H + 1) ≤ n) (hH : 3 ≤ H) :
    (5 / 4 + Econst / 2) * (H : ℝ) - Real.logb 2 (H : ℝ) - 5 ≤ (Bcount n : ℝ) := by
  obtain ⟨κ, hκ1, hκ2⟩ : ∃ κ, 2 ^ κ ≤ H ∧ H < 2 ^ (κ + 1) :=
    ⟨Nat.log 2 H, Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) H⟩
  have hκH : κ ≤ H := by
    have := nat_lt_two_pow κ
    omega
  have h1 := B_nat hn hH hκH
  have h2 := n1_real hκH hκ2
  have h3 := n2_real hH
  have h4 := kappa_le_logb (by omega) hκ1
  have h5 : ((H + ∑ j ∈ Finset.range κ, (H - (j + 1)) / (2 * (2 ^ (j + 1) - 1)) +
      ((H - 3) / 4 + 1) : ℕ) : ℝ) ≤ (Bcount n : ℝ) := by exact_mod_cast h1
  push_cast at h2 h5
  push_cast at h3
  linarith

end SequenceNicolas.Counting
