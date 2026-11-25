module

public import Mathlib
public import SequenceNicolas.Recursion
public import SequenceNicolas.Families
public import SequenceNicolas.Counting
public import SequenceNicolas.CountingA

@[expose] public section

/-!
# Proposition `prop:nicolascount`

The exponents of the three families of Nicolas: `a + (2^a - 11)/3` with `a ≥ 3` odd,
`2^r + r - 2` with `r ≥ 1`, and `a + (2^a - 10)/3` with `a ≥ 4` even.  In natural numbers the
exponents `a + (2^a - δ)/3` are written `(3a + 2^a - δ)/3`; the division is exact.
-/

namespace SequenceNicolas.NicolasCount

open SequenceNicolas.Recursion SequenceNicolas.Families SequenceNicolas.Counting

open scoped Classical

/-- `a + (2^a - 11)/3`. -/
def e11 (a : ℕ) : ℕ := (3 * a + 2 ^ a - 11) / 3

/-- `a + (2^a - 10)/3`. -/
def e10 (a : ℕ) : ℕ := (3 * a + 2 ^ a - 10) / 3

theorem two_mul_le_pow (a : ℕ) : 2 * a ≤ 2 ^ a := by
  induction a with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
      have e : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      omega

theorem e11_spec {a : ℕ} (ha : 3 ≤ a) (hodd : a % 2 = 1) : 3 * e11 a + 11 = 3 * a + 2 ^ a := by
  have hm := two_pow_mod_three_odd hodd
  have h8 : 8 ≤ 2 ^ a := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  unfold e11
  omega

theorem e10_spec {a : ℕ} (ha : 4 ≤ a) (hev : a % 2 = 0) : 3 * e10 a + 10 = 3 * a + 2 ^ a := by
  have hm := two_pow_mod_three_even hev
  have h8 : 16 ≤ 2 ^ a := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  unfold e10
  omega

theorem pow_lt_of_lt {a b : ℕ} (h : a < b) : 2 ^ a < 2 ^ b := by
  exact Nat.pow_lt_pow_right (by norm_num) h

theorem spec_inj {δ a a' x x' : ℕ} (h : 3 * x + δ = 3 * a + 2 ^ a)
    (h' : 3 * x' + δ = 3 * a' + 2 ^ a') (hx : x = x') : a = a' := by
  rcases lt_trichotomy a a' with hl | he | hg
  · have := pow_lt_of_lt hl
    omega
  · exact he
  · have := pow_lt_of_lt hg
    omega

/-- The exponents `a + (2^a - 11)/3`, `a ≥ 3` odd, that are at most `n`. -/
noncomputable def Aset (n : ℕ) : Finset ℕ :=
  ((Finset.range (n + 2)).filter (fun a => 3 ≤ a ∧ a % 2 = 1 ∧ e11 a ≤ n)).image e11

/-- The exponents `2^r + r - 2`, `r ≥ 1`, that are at most `n`. -/
noncomputable def Pset (n : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 n).filter (fun r => 2 ^ r + r - 2 ≤ n)).image (fun r => 2 ^ r + r - 2)

/-- The exponents `a + (2^a - 10)/3`, `a ≥ 4` even, that are at most `n`. -/
noncomputable def Qset (n : ℕ) : Finset ℕ :=
  ((Finset.range (n + 2)).filter (fun a => 4 ≤ a ∧ a % 2 = 0 ∧ e10 a ≤ n)).image e10

/-- `A_N(n)`. -/
noncomputable def AN (n : ℕ) : ℕ := (Aset n).card

/-- `B_N(n)`. -/
noncomputable def BN (n : ℕ) : ℕ := (Pset n ∪ Qset n).card

theorem log_facts {n : ℕ} (hn : 1 ≤ n) :
    2 ^ Nat.log 2 n ≤ n ∧ n < 2 ^ (Nat.log 2 n + 1) ∧
    (Nat.log 2 n : ℝ) ≤ Real.logb 2 (n : ℝ) ∧ Real.logb 2 (n : ℝ) < Nat.log 2 n + 1 := by
  have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  refine ⟨h1, h2, kappa_le_logb hn h1, ?_⟩
  have h3 : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by exact_mod_cast h2
  have h4 : Real.logb 2 (n : ℝ) < Real.logb 2 ((2 : ℝ) ^ (Nat.log 2 n + 1)) :=
    Real.logb_lt_logb (by norm_num) (by exact_mod_cast hn) h3
  have h5 : Real.logb 2 ((2 : ℝ) ^ (Nat.log 2 n + 1)) = ((Nat.log 2 n + 1 : ℕ) : ℝ) := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; ring
  rw [h5] at h4
  push_cast at h4
  exact h4

/-! ### `A_N` -/

theorem Aset_card (n : ℕ) :
    (Aset n).card = ((Finset.range (n + 2)).filter (fun a => 3 ≤ a ∧ a % 2 = 1 ∧ e11 a ≤ n)).card := by
  unfold Aset
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  have ha' := (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2
  have hb' := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
  exact spec_inj (e11_spec ha'.1 ha'.2.1) (e11_spec hb'.1 hb'.2.1) hab

theorem A_lower {n : ℕ} (hn : 1 ≤ n) : (Nat.log 2 n - 1) / 2 ≤ AN n := by
  obtain ⟨h1, h2, _, _⟩ := log_facts hn
  unfold AN
  rw [Aset_card]
  set L := Nat.log 2 n with hL
  have hsub : (Finset.range ((L - 1) / 2)).image (fun u => 2 * u + 3) ⊆
      (Finset.range (n + 2)).filter (fun a => 3 ≤ a ∧ a % 2 = 1 ∧ e11 a ≤ n) := by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ha
    have hu' := Finset.mem_range.1 hu
    have haL : 2 * u + 3 ≤ L := by omega
    have hp : 2 ^ (2 * u + 3) ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) haL
    have hlt := nat_lt_two_pow L
    have hs := e11_spec (a := 2 * u + 3) (by omega) (by omega)
    have h2a := two_mul_le_pow (2 * u + 3)
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, by omega, by omega, ?_⟩
    omega
  have hc := Finset.card_le_card hsub
  have hinj : Function.Injective (fun u : ℕ => 2 * u + 3) := by
    intro x y h
    have h' : 2 * x + 3 = 2 * y + 3 := h
    omega
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range] at hc
  exact hc

theorem A_upper {n : ℕ} (hn : 1 ≤ n) : AN n ≤ Nat.log 2 n / 2 + 1 := by
  obtain ⟨h1, h2, _, _⟩ := log_facts hn
  unfold AN
  rw [Aset_card]
  set L := Nat.log 2 n with hL
  have hsub : (Finset.range (n + 2)).filter (fun a => 3 ≤ a ∧ a % 2 = 1 ∧ e11 a ≤ n) ⊆
      (Finset.range (L / 2 + 1)).image (fun u => 2 * u + 3) := by
    intro a ha
    obtain ⟨_, ha1, ha2, ha3⟩ := Finset.mem_filter.1 ha
    have hs := e11_spec ha1 ha2
    have hP : 2 ^ a ≤ 3 * n + 2 := by omega
    have haL : a < L + 4 := by
      by_contra hc
      push Not at hc
      have hp : 2 ^ (L + 4) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hc
      have e : 2 ^ (L + 4) = 8 * 2 ^ (L + 1) := by ring
      omega
    refine Finset.mem_image.2 ⟨(a - 3) / 2, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · show 2 * ((a - 3) / 2) + 3 = a
      omega
  have hc := Finset.card_le_card hsub
  have h3 := Finset.card_image_le (s := Finset.range (L / 2 + 1)) (f := fun u => 2 * u + 3)
  rw [Finset.card_range] at h3
  omega

theorem A_real {n : ℕ} (hn : 1 ≤ n) :
    |(AN n : ℝ) - Real.logb 2 (n : ℝ) / 2| ≤ 2 := by
  obtain ⟨_, _, h3, h4⟩ := log_facts hn
  have a1 := A_lower hn
  have a2 := A_upper hn
  have b1 : Nat.log 2 n ≤ 2 * AN n + 2 := by omega
  have b2 : 2 * AN n ≤ Nat.log 2 n + 2 := by omega
  have c1 : ((Nat.log 2 n : ℕ) : ℝ) ≤ 2 * (AN n : ℝ) + 2 := by exact_mod_cast b1
  have c2 : 2 * (AN n : ℝ) ≤ ((Nat.log 2 n : ℕ) : ℝ) + 2 := by exact_mod_cast b2
  rw [abs_le]
  constructor <;> linarith

/-! ### `B_N` -/

theorem Pset_card (n : ℕ) :
    (Pset n).card = ((Finset.Icc 1 n).filter (fun r => 2 ^ r + r - 2 ≤ n)).card := by
  unfold Pset
  apply Finset.card_image_of_injOn
  intro r hr s hs h
  have hr' := (Finset.mem_Icc.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hr)).1).1
  have hs' := (Finset.mem_Icc.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hs)).1).1
  have h' : 2 ^ r + r - 2 = 2 ^ s + s - 2 := h
  clear h
  have h2r : 2 ≤ 2 ^ r := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr'
  have h2s : 2 ≤ 2 ^ s := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs'
  rcases lt_trichotomy r s with hl | he | hg
  · have := pow_lt_of_lt hl
    omega
  · exact he
  · have := pow_lt_of_lt hg
    omega

theorem P_lower {n : ℕ} (hn : 1 ≤ n) : Nat.log 2 n - 1 ≤ (Pset n).card := by
  obtain ⟨h1, h2, _, _⟩ := log_facts hn
  rw [Pset_card]
  set L := Nat.log 2 n with hL
  have hsub : Finset.Icc 1 (L - 1) ⊆ (Finset.Icc 1 n).filter (fun r => 2 ^ r + r - 2 ≤ n) := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.1 hr
    have hp : 2 ^ r ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by norm_num) hr2
    have hlt := nat_lt_two_pow r
    have e : 2 ^ L = 2 * 2 ^ (L - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hr1, by omega⟩, by omega⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  omega

theorem P_upper {n : ℕ} (hn : 1 ≤ n) : (Pset n).card ≤ Nat.log 2 n + 1 := by
  obtain ⟨h1, h2, _, _⟩ := log_facts hn
  rw [Pset_card]
  set L := Nat.log 2 n with hL
  have hsub : (Finset.Icc 1 n).filter (fun r => 2 ^ r + r - 2 ≤ n) ⊆ Finset.Icc 1 (L + 1) := by
    intro r hr
    obtain ⟨hr0, hr3⟩ := Finset.mem_filter.1 hr
    obtain ⟨hr1, _⟩ := Finset.mem_Icc.1 hr0
    have hrL : r < L + 2 := by
      by_contra hc
      push Not at hc
      have hp : 2 ^ (L + 2) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hc
      have e : 2 ^ (L + 2) = 2 * 2 ^ (L + 1) := by ring
      omega
    rw [Finset.mem_Icc]
    omega
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  omega

theorem Qset_card (n : ℕ) :
    (Qset n).card = ((Finset.range (n + 2)).filter (fun a => 4 ≤ a ∧ a % 2 = 0 ∧ e10 a ≤ n)).card := by
  unfold Qset
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  have ha' := (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2
  have hb' := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
  exact spec_inj (e10_spec ha'.1 ha'.2.1) (e10_spec hb'.1 hb'.2.1) hab

theorem Q_lower {n : ℕ} (hn : 1 ≤ n) : (Nat.log 2 n - 2) / 2 ≤ (Qset n).card := by
  obtain ⟨h1, h2, _, _⟩ := log_facts hn
  rw [Qset_card]
  set L := Nat.log 2 n with hL
  have hsub : (Finset.range ((L - 2) / 2)).image (fun u => 2 * u + 4) ⊆
      (Finset.range (n + 2)).filter (fun a => 4 ≤ a ∧ a % 2 = 0 ∧ e10 a ≤ n) := by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ha
    have hu' := Finset.mem_range.1 hu
    have haL : 2 * u + 4 ≤ L := by omega
    have hp : 2 ^ (2 * u + 4) ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) haL
    have hlt := nat_lt_two_pow L
    have hs := e10_spec (a := 2 * u + 4) (by omega) (by omega)
    have h2a := two_mul_le_pow (2 * u + 4)
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, by omega, by omega, ?_⟩
    omega
  have hc := Finset.card_le_card hsub
  have hinj : Function.Injective (fun u : ℕ => 2 * u + 4) := by
    intro x y h
    have h' : 2 * x + 4 = 2 * y + 4 := h
    omega
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range] at hc
  exact hc

theorem Q_upper {n : ℕ} (hn : 1 ≤ n) : (Qset n).card ≤ Nat.log 2 n / 2 + 1 := by
  obtain ⟨h1, h2, _, _⟩ := log_facts hn
  rw [Qset_card]
  set L := Nat.log 2 n with hL
  have hsub : (Finset.range (n + 2)).filter (fun a => 4 ≤ a ∧ a % 2 = 0 ∧ e10 a ≤ n) ⊆
      (Finset.range (L / 2 + 1)).image (fun u => 2 * u + 4) := by
    intro a ha
    obtain ⟨_, ha1, ha2, ha3⟩ := Finset.mem_filter.1 ha
    have hs := e10_spec ha1 ha2
    have hP : 2 ^ a ≤ 3 * n := by omega
    have haL : a < L + 3 := by
      by_contra hc
      push Not at hc
      have hp : 2 ^ (L + 3) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hc
      have e : 2 ^ (L + 3) = 4 * 2 ^ (L + 1) := by ring
      omega
    refine Finset.mem_image.2 ⟨(a - 4) / 2, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · show 2 * ((a - 4) / 2) + 4 = a
      omega
  have hc := Finset.card_le_card hsub
  have h3 := Finset.card_image_le (s := Finset.range (L / 2 + 1)) (f := fun u => 2 * u + 4)
  rw [Finset.card_range] at h3
  omega

/-- The exponents `2^r + r - 2` and `a + (2^a - 10)/3` are distinct
(Theorems `thm:leading` and `thm:nonmembers`). -/
theorem PQ_disjoint (n : ℕ) : Disjoint (Pset n) (Qset n) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  obtain ⟨r, hr, hrx⟩ := Finset.mem_image.1 hx1
  obtain ⟨a, ha, hax⟩ := Finset.mem_image.1 hx2
  have hr1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 hr).1).1
  have ha' := (Finset.mem_filter.1 ha).2
  obtain ⟨K, h, hh, h3, hodd, hK3, _, hspec⟩ := nicolas_three_fwd ha'.1 ha'.2.1
  have hs := e10_spec ha'.1 ha'.2.1
  have hxe : x = K + h - 3 := by
    have : e10 a = K + h - 3 := by omega
    omega
  have h2r : 2 ≤ 2 ^ r := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr1
  have hp : 2 ^ h ≥ 8 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) h3
  have he : 2 ^ (h + 1) = 2 * 2 ^ h := by ring
  have ea : 2 ^ a = 2 ^ (h + 1) := by rw [hh]
  have hK2 : 2 ≤ K := by omega
  have hfK : hfun K = h := hfun_of_bounds hK2 (by omega) (by omega)
  have hno := (nicolas_one x).2 ⟨r, hr1, by omega⟩
  exact hno ⟨K, hK2, by unfold beta; omega⟩

theorem B_real {n : ℕ} (hn : 1 ≤ n) :
    |(BN n : ℝ) - 3 / 2 * Real.logb 2 (n : ℝ)| ≤ 4 := by
  obtain ⟨_, _, h3, h4⟩ := log_facts hn
  have p1 := P_lower hn
  have p2 := P_upper hn
  have q1 := Q_lower hn
  have q2 := Q_upper hn
  have hd := card_union_disj (PQ_disjoint n)
  have hB : BN n = (Pset n).card + (Qset n).card := hd
  have b1 : 3 * Nat.log 2 n ≤ 2 * BN n + 5 := by omega
  have b2 : 2 * BN n ≤ 3 * Nat.log 2 n + 4 := by omega
  have c1 : 3 * ((Nat.log 2 n : ℕ) : ℝ) ≤ 2 * (BN n : ℝ) + 5 := by exact_mod_cast b1
  have c2 : 2 * (BN n : ℝ) ≤ 3 * ((Nat.log 2 n : ℕ) : ℝ) + 4 := by exact_mod_cast b2
  rw [abs_le]
  constructor <;> linarith

end SequenceNicolas.NicolasCount
