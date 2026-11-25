module

public import Mathlib
public import SequenceNicolas.Core

@[expose] public section

/-!
# The greedy lemma, the leading term and the state recursion

This module formalizes Sections "The largest element of `T`" and "A recursion on small
integers" of the paper, except for the closed formulas already proved in
`SequenceNicolas.Core`:

* `InE J V` : `V ∈ 𝓔_J`, i.e. `V` is a sum of distinct terms `j 2^j` with `1 ≤ j ≤ J`;
* `repr_unique`, `greedy_iff` : Lemma `lem:greedy`;
* `hfun`, `beta` : `h(K) = ⌈log₂ K⌉` (the least `g` with `K ≤ 2^g`) and `β(K) = K + h(K)`;
* `beta_strictMono`, `beta_range`, `leading_beta`, `leading_state`, `inE_two_pow_iff`,
  `amem_gap`, `amem_iff_state` : Theorem `thm:leading` (1), (2), (3) and its last statement;
* `IsState`, `Succ`, `IsS`, `exists_S`, `step_main` : Theorem `thm:step`;
* `Run`, `run_sound`, `run_complete`, `int_bound` : Algorithm `alg:membership` and
  Corollary `cor:algo`;
* `least_char`, `fails_iff`, `least_two`, `IsS_unique` : Lemma `lem:least`.
-/

namespace SequenceNicolas.Recursion

/-- `InE J V` : `V ∈ 𝓔_J`, a sum of distinct terms `j 2^j` with `1 ≤ j ≤ J`
(equation `eq:EJ`). -/
def InE (J V : ℕ) : Prop :=
  ∃ T : Finset ℕ, T ⊆ Finset.Icc 1 J ∧ ∑ j ∈ T, j * 2 ^ j = V

theorem InE_zero (J : ℕ) : InE J 0 :=
  ⟨∅, Finset.empty_subset _, Finset.sum_empty⟩

theorem sum_lt_of_subset {T : Finset ℕ} {m : ℕ} (h : T ⊆ Finset.Icc 1 m) :
    ∑ j ∈ T, j * 2 ^ j < (m + 1) * 2 ^ (m + 1) := by
  have h1 : ∑ j ∈ T, j * 2 ^ j ≤ ∑ j ∈ Finset.Icc 1 m, j * 2 ^ j :=
    Finset.sum_le_sum_of_subset h
  have h2 := SequenceNicolas.Core.sum_j_two_pow m
  have h3 : 2 ^ 1 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : (m + 1) * 2 ^ (m + 1) = m * 2 ^ (m + 1) + 2 ^ (m + 1) := by ring
  have h5 : (2 : ℕ) ^ 1 = 2 := by norm_num
  omega

/-- Every element of `𝓔_J` is smaller than `(J+1) 2^{J+1}` (Lemma `lem:sum`). -/
theorem InE_lt {J V : ℕ} (h : InE J V) : V < (J + 1) * 2 ^ (J + 1) := by
  obtain ⟨T, hT, hs⟩ := h
  rw [← hs]
  exact sum_lt_of_subset hT

theorem erase_sub {T : Finset ℕ} {J : ℕ} (h : T ⊆ Finset.Icc 1 (J + 1)) :
    T.erase (J + 1) ⊆ Finset.Icc 1 J := by
  intro x hx
  rcases Finset.mem_erase.1 hx with ⟨hne, hxT⟩
  have h1 := Finset.mem_Icc.1 (h hxT)
  exact Finset.mem_Icc.2 ⟨h1.1, by omega⟩

theorem not_mem_sub {T : Finset ℕ} {J : ℕ} (h : T ⊆ Finset.Icc 1 (J + 1)) (hn : J + 1 ∉ T) :
    T ⊆ Finset.Icc 1 J := by
  intro x hx
  have h1 := Finset.mem_Icc.1 (h hx)
  have h3 : x ≠ J + 1 := fun e => hn (by rw [← e]; exact hx)
  exact Finset.mem_Icc.2 ⟨h1.1, by omega⟩

theorem sum_erase_eq {T : Finset ℕ} {n : ℕ} (h : n ∈ T) :
    ∑ j ∈ T, j * 2 ^ j = n * 2 ^ n + ∑ j ∈ T.erase n, j * 2 ^ j :=
  (Finset.add_sum_erase T (fun j => j * 2 ^ j) h).symm

/-- Uniqueness of the representing set (Lemma `lem:greedy`). -/
theorem repr_unique : ∀ (J : ℕ) (T₁ T₂ : Finset ℕ), T₁ ⊆ Finset.Icc 1 J →
    T₂ ⊆ Finset.Icc 1 J → ∑ j ∈ T₁, j * 2 ^ j = ∑ j ∈ T₂, j * 2 ^ j → T₁ = T₂ := by
  intro J
  induction J with
  | zero =>
    intro T₁ T₂ h1 h2 _
    have e : Finset.Icc 1 0 = (∅ : Finset ℕ) := by
      rfl
    rw [e] at h1 h2
    rw [Finset.subset_empty.1 h1, Finset.subset_empty.1 h2]
  | succ J ih =>
    intro T₁ T₂ h1 h2 hs
    by_cases a1 : J + 1 ∈ T₁
    · by_cases a2 : J + 1 ∈ T₂
      · have e1 := sum_erase_eq a1
        have e2 := sum_erase_eq a2
        have heq := ih (T₁.erase (J + 1)) (T₂.erase (J + 1)) (erase_sub h1) (erase_sub h2)
          (by omega)
        ext x
        by_cases hx : x = J + 1
        · subst hx
          exact ⟨fun _ => a2, fun _ => a1⟩
        · have hh := Finset.ext_iff.1 heq x
          simp only [Finset.mem_erase] at hh
          constructor
          · intro h
            exact (hh.1 ⟨hx, h⟩).2
          · intro h
            exact (hh.2 ⟨hx, h⟩).2
      · exfalso
        have e1 := sum_erase_eq a1
        have h3 := sum_lt_of_subset (not_mem_sub h2 a2)
        omega
    · by_cases a2 : J + 1 ∈ T₂
      · exfalso
        have e2 := sum_erase_eq a2
        have h3 := sum_lt_of_subset (not_mem_sub h1 a1)
        omega
      · exact ih T₁ T₂ (not_mem_sub h1 a1) (not_mem_sub h2 a2) hs

/-- Lemma `lem:greedy` (last statement): if `m + 1` is the largest `j ≤ J` with `j 2^j ≤ V`, then
`V ∈ 𝓔_J` iff `V - (m+1) 2^{m+1} ∈ 𝓔_m`. -/
theorem greedy_iff {J V m : ℕ} (hmJ : m + 1 ≤ J) (hjV : (m + 1) * 2 ^ (m + 1) ≤ V)
    (hmax : ∀ i, m + 1 < i → i ≤ J → V < i * 2 ^ i) :
    InE J V ↔ InE m (V - (m + 1) * 2 ^ (m + 1)) := by
  constructor
  · rintro ⟨T, hTJ, hs⟩
    have hle : ∀ x ∈ T, x ≤ m + 1 := by
      intro x hx
      by_contra hc
      push Not at hc
      have hxJ : x ≤ J := (Finset.mem_Icc.1 (hTJ hx)).2
      have h1 : x * 2 ^ x ≤ ∑ j ∈ T, j * 2 ^ j :=
        Finset.single_le_sum (f := fun j => j * 2 ^ j) (fun _ _ => Nat.zero_le _) hx
      have h2 := hmax x hc hxJ
      omega
    have hmem : m + 1 ∈ T := by
      by_contra hn
      have hsub : T ⊆ Finset.Icc 1 m := by
        intro x hx
        have h1 := Finset.mem_Icc.1 (hTJ hx)
        have h2 := hle x hx
        have h3 : x ≠ m + 1 := fun e => hn (by rw [← e]; exact hx)
        exact Finset.mem_Icc.2 ⟨h1.1, by omega⟩
      have h4 := sum_lt_of_subset hsub
      omega
    refine ⟨T.erase (m + 1), ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_erase.1 hx with ⟨hne, hxT⟩
      have h1 := Finset.mem_Icc.1 (hTJ hxT)
      have h2 := hle x hxT
      exact Finset.mem_Icc.2 ⟨h1.1, by omega⟩
    · have h' := sum_erase_eq hmem
      omega
  · rintro ⟨T, hT, hs⟩
    have hnot : m + 1 ∉ T := fun h => by
      have := (Finset.mem_Icc.1 (hT h)).2
      omega
    refine ⟨insert (m + 1) T, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx'
      · exact Finset.mem_Icc.2 ⟨by omega, hmJ⟩
      · have h1 := Finset.mem_Icc.1 (hT hx')
        exact Finset.mem_Icc.2 ⟨h1.1, by omega⟩
    · rw [Finset.sum_insert hnot]
      omega

/-- The case `J = m + 1` of `greedy_iff`: the largest term is `(m+1) 2^{m+1}` itself. -/
theorem inE_top_iff {m V : ℕ} (hV : (m + 1) * 2 ^ (m + 1) ≤ V) :
    InE (m + 1) V ↔ InE m (V - (m + 1) * 2 ^ (m + 1)) :=
  greedy_iff (le_refl _) hV (fun i hi hi' => absurd hi' (by omega))

/-! ### The function `β` -/

theorem nat_lt_two_pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    omega

theorem exists_hfun (K : ℕ) : ∃ g : ℕ, K ≤ 2 ^ g := ⟨K, (nat_lt_two_pow K).le⟩

/-- `h(K) = ⌈log₂ K⌉`, the least `g` with `K ≤ 2^g` (equation `eq:beta`). -/
def hfun (K : ℕ) : ℕ := Nat.find (exists_hfun K)

/-- `β(K) = K + h(K)` (equation `eq:beta`). -/
def beta (K : ℕ) : ℕ := K + hfun K

theorem hfun_ge (K : ℕ) : K ≤ 2 ^ hfun K := Nat.find_spec (exists_hfun K)

theorem hfun_le {K g : ℕ} (hg : K ≤ 2 ^ g) : hfun K ≤ g :=
  Nat.find_min' (exists_hfun K) hg

theorem hfun_lt_min {K g : ℕ} (hg : g < hfun K) : 2 ^ g < K := by
  have := Nat.find_min (exists_hfun K) hg
  omega

theorem hfun_mono {K K' : ℕ} (h : K ≤ K') : hfun K ≤ hfun K' :=
  hfun_le (le_trans h (hfun_ge K'))

theorem hfun_spec {K : ℕ} (hK : 2 ≤ K) :
    1 ≤ hfun K ∧ K ≤ 2 ^ hfun K ∧ 2 ^ hfun K < 2 * K := by
  have hge := hfun_ge K
  have h1 : 1 ≤ hfun K := by
    by_contra hc
    have h0 : hfun K = 0 := by omega
    rw [h0] at hge
    norm_num at hge
    omega
  obtain ⟨g', hg'⟩ : ∃ g', hfun K = g' + 1 := ⟨hfun K - 1, by omega⟩
  have h2 := hfun_lt_min (K := K) (g := g') (by omega)
  have h3 : 2 ^ (g' + 1) = 2 * 2 ^ g' := by ring
  refine ⟨h1, hge, ?_⟩
  rw [hg', h3]
  omega

theorem pow2_unique {K g h : ℕ} (h1 : K ≤ 2 ^ g) (h2 : 2 ^ g < 2 * K) (h3 : K ≤ 2 ^ h)
    (h4 : 2 ^ h < 2 * K) : g = h := by
  rcases lt_trichotomy g h with hlt | heq | hgt
  · exfalso
    have h5 : 2 ^ (g + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hlt
    have e : 2 ^ (g + 1) = 2 * 2 ^ g := by ring
    omega
  · exact heq
  · exfalso
    have h5 : 2 ^ (h + 1) ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hgt
    have e : 2 ^ (h + 1) = 2 * 2 ^ h := by ring
    omega

theorem hfun_of_bounds {K g : ℕ} (hK : 2 ≤ K) (h1 : K ≤ 2 ^ g) (h2 : 2 ^ g < 2 * K) :
    hfun K = g := by
  obtain ⟨_, a, b⟩ := hfun_spec hK
  exact pow2_unique a b h1 h2

theorem hfun_succ (K : ℕ) :
    hfun (K + 1) = hfun K ∨ (K = 2 ^ hfun K ∧ hfun (K + 1) = hfun K + 1) := by
  have h1 : hfun K ≤ hfun (K + 1) := hfun_mono (Nat.le_succ K)
  have hp : 0 < 2 ^ hfun K := by positivity
  have hge := hfun_ge K
  have e : 2 ^ (hfun K + 1) = 2 * 2 ^ hfun K := by ring
  have h2 : hfun (K + 1) ≤ hfun K + 1 := hfun_le (by omega)
  by_cases hc : hfun (K + 1) = hfun K
  · exact Or.inl hc
  · right
    have hc' : hfun (K + 1) = hfun K + 1 := by omega
    refine ⟨?_, hc'⟩
    by_contra hne
    have hlt : K + 1 ≤ 2 ^ hfun K := by omega
    have := hfun_le hlt
    omega

theorem beta_lt_succ (K : ℕ) : beta K < beta (K + 1) := by
  have : hfun K ≤ hfun (K + 1) := hfun_mono (Nat.le_succ K)
  unfold beta
  omega

/-- Theorem `thm:leading` (2): `β` is strictly increasing. -/
theorem beta_strictMono : StrictMono beta := strictMono_nat_of_lt_succ beta_lt_succ

theorem beta_inj {K K' : ℕ} (h : beta K = beta K') : K = K' := beta_strictMono.injective h

theorem beta_two_pow {r : ℕ} (hr : 1 ≤ r) : beta (2 ^ r) = 2 ^ r + r := by
  have hp : 2 ^ 1 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  have e : (2 : ℕ) ^ 1 = 2 := by norm_num
  have : hfun (2 ^ r) = r := hfun_of_bounds (by omega) (le_refl _) (by omega)
  unfold beta
  omega

theorem beta_two_pow_succ {r : ℕ} : beta (2 ^ r + 1) = 2 ^ r + r + 2 := by
  have hp : 0 < 2 ^ r := by positivity
  have e : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
  have : hfun (2 ^ r + 1) = r + 1 := hfun_of_bounds (by omega) (by omega) (by omega)
  unfold beta
  omega

/-- Theorem `thm:leading` (2): for `b ≥ 3`, `b` is a value of `β` on `{2, 3, …}` iff `b` is not of
the form `2^r + r + 1` with `r ≥ 1`. -/
theorem beta_range {b : ℕ} (hb : 3 ≤ b) :
    (∃ K, 2 ≤ K ∧ beta K = b) ↔ ∀ r, 1 ≤ r → b ≠ 2 ^ r + r + 1 := by
  constructor
  · rintro ⟨K, hK, hKb⟩ r hr hbr
    have h1 := beta_two_pow hr
    have h2 := beta_two_pow_succ (r := r)
    have lt1 : beta (2 ^ r) < beta K := by omega
    have lt2 : beta K < beta (2 ^ r + 1) := by omega
    have a1 := beta_strictMono.lt_iff_lt.1 lt1
    have a2 := beta_strictMono.lt_iff_lt.1 lt2
    omega
  · intro h
    have hb2 : beta 2 = 3 := by
      have : hfun 2 = 1 := hfun_of_bounds (by norm_num) (by norm_num) (by norm_num)
      unfold beta
      omega
    have hP2 : (fun K => beta K ≤ b) 2 := by
      show beta 2 ≤ b
      omega
    have hG1 : 2 ≤ Nat.findGreatest (fun K => beta K ≤ b) b :=
      Nat.le_findGreatest (by omega) hP2
    have hG2 : beta (Nat.findGreatest (fun K => beta K ≤ b) b) ≤ b :=
      Nat.findGreatest_spec (P := fun K => beta K ≤ b) (m := 2) (by omega) hP2
    have hG3 : ∀ K, K ≤ b → beta K ≤ b → K ≤ Nat.findGreatest (fun K => beta K ≤ b) b :=
      fun K hK hb' => Nat.le_findGreatest hK hb'
    generalize Nat.findGreatest (fun K => beta K ≤ b) b = K0 at hG1 hG2 hG3
    have hK2 : 2 ≤ K0 := hG1
    have hle : beta K0 ≤ b := hG2
    have hnext : b < beta (K0 + 1) := by
      by_contra hc
      push Not at hc
      have h1 : K0 + 1 ≤ beta (K0 + 1) := by
        unfold beta
        omega
      have h2 := hG3 (K0 + 1) (by omega) hc
      omega
    have e1 : beta K0 = K0 + hfun K0 := rfl
    have e2 : beta (K0 + 1) = K0 + 1 + hfun (K0 + 1) := rfl
    rcases hfun_succ K0 with hh | ⟨hK, hh⟩
    · exact ⟨K0, hK2, by omega⟩
    · by_cases hbe : b = beta K0
      · exact ⟨K0, hK2, hbe.symm⟩
      · exfalso
        have hg : 1 ≤ hfun K0 := by
          by_contra hc
          have h0 : hfun K0 = 0 := by omega
          rw [h0] at hK
          norm_num at hK
          omega
        exact h (hfun K0) hg (by omega)

/-! ### The leading term -/

/-- Theorem `thm:leading` (1): if `T` represents `2^b`, `b ≥ 3`, and `K = max T`, then `K ≥ 2` and
`β(K) = b`. -/
theorem leading_beta {T : Finset ℕ} (hT : ∀ j ∈ T, 1 ≤ j) {b K : ℕ} (hb : 3 ≤ b)
    (hK : K ∈ T) (hmax : ∀ j ∈ T, j ≤ K) (hsum : ∑ j ∈ T, j * 2 ^ j = 2 ^ b) :
    2 ≤ K ∧ beta K = b := by
  obtain ⟨h2, g, h1, h3, hbg⟩ := SequenceNicolas.Core.leading_term hT hb hK hmax hsum
  have : hfun K = g := hfun_of_bounds h2 h1 h3
  refine ⟨h2, ?_⟩
  unfold beta
  omega

/-- Theorem `thm:leading` (3): `0 ≤ 2^h - K ≤ K - 2`. -/
theorem leading_state {K : ℕ} (hK : 2 ≤ K) :
    K ≤ 2 ^ hfun K ∧ 2 ^ hfun K - K + 1 ≤ K - 1 := by
  obtain ⟨h1, h2, h3⟩ := hfun_spec hK
  obtain ⟨g', hg'⟩ : ∃ g', hfun K = g' + 1 := ⟨hfun K - 1, by omega⟩
  have h4 := hfun_lt_min (K := K) (g := g') (by omega)
  have e : 2 ^ (g' + 1) = 2 * 2 ^ g' := by ring
  rw [hg'] at h2 h3 ⊢
  refine ⟨h2, ?_⟩
  omega

/-- If `2^b ∈ 𝓔_J` with `b ≥ 3`, there is `K ≥ 2` with `β(K) = b` and `2^b ∈ 𝓔_K`
(`K` is the largest element of the representing set). -/
theorem exists_top {J b : ℕ} (hb : 3 ≤ b) (h : InE J (2 ^ b)) :
    ∃ K, 2 ≤ K ∧ beta K = b ∧ InE K (2 ^ b) := by
  obtain ⟨T, hTJ, hs⟩ := h
  have hp : 0 < 2 ^ b := by positivity
  rcases T.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Finset.sum_empty] at hs
    omega
  · have hT1 : ∀ j ∈ T, 1 ≤ j := fun j hj => (Finset.mem_Icc.1 (hTJ hj)).1
    have hMmem : T.max' hne ∈ T := Finset.max'_mem T hne
    have hle : ∀ j ∈ T, j ≤ T.max' hne := fun j hj => Finset.le_max' T j hj
    generalize T.max' hne = M at hMmem hle
    obtain ⟨hM2, hMb⟩ := leading_beta hT1 hb hMmem hle hs
    refine ⟨M, hM2, hMb, T, ?_, hs⟩
    intro j hj
    exact Finset.mem_Icc.2 ⟨hT1 j hj, hle j hj⟩

/-- Theorem `thm:leading` (3): with `K = m + 1 ≥ 2`, `2^{β(K)} ∈ 𝓔` iff
`2^K (2^{h(K)} - K) ∈ 𝓔_{K-1}`. -/
theorem inE_two_pow_iff {m : ℕ} (hm : 1 ≤ m) :
    (∃ J, InE J (2 ^ beta (m + 1))) ↔ InE m (2 ^ (m + 1) * (2 ^ hfun (m + 1) - (m + 1))) := by
  have hK : 2 ≤ m + 1 := by omega
  obtain ⟨hh1, hh2, hh3⟩ := hfun_spec hK
  obtain ⟨w, hw⟩ : ∃ w, 2 ^ hfun (m + 1) = (m + 1) + w :=
    ⟨2 ^ hfun (m + 1) - (m + 1), by omega⟩
  have hwv : 2 ^ hfun (m + 1) - (m + 1) = w := by omega
  have hV : 2 ^ beta (m + 1) = (m + 1) * 2 ^ (m + 1) + 2 ^ (m + 1) * w := by
    show 2 ^ ((m + 1) + hfun (m + 1)) = _
    rw [pow_add, hw]
    ring
  have hle : (m + 1) * 2 ^ (m + 1) ≤ 2 ^ beta (m + 1) := by omega
  have e : 2 ^ beta (m + 1) - (m + 1) * 2 ^ (m + 1) = 2 ^ (m + 1) * w := by omega
  have hb3 : 3 ≤ beta (m + 1) := by
    unfold beta
    omega
  rw [hwv]
  constructor
  · rintro ⟨J, hJ⟩
    obtain ⟨K, hK2, hKb, hIn⟩ := exists_top hb3 hJ
    have hKm : K = m + 1 := beta_inj hKb
    subst hKm
    have := (inE_top_iff hle).1 hIn
    rw [e] at this
    exact this
  · intro h
    refine ⟨m + 1, (inE_top_iff hle).2 ?_⟩
    rw [e]
    exact h

/-- `a ∈ 𝓐`: `2^a` lies in the image of `c` (equation `eq:Adef`). -/
def Amem (a : ℕ) : Prop := ∃ n : ℕ, SequenceNicolas.Core.c n = 2 ^ a

theorem amem_iff_InE (a : ℕ) : Amem a ↔ ∃ J, InE J (2 ^ (a + 3)) := by
  unfold Amem
  rw [SequenceNicolas.Core.equiv_repr a]
  constructor
  · rintro ⟨T, hT, hs⟩
    refine ⟨∑ j ∈ T, j, T, ?_, hs⟩
    intro j hj
    have h1 : j ≤ ∑ i ∈ T, i :=
      Finset.single_le_sum (f := fun i => i) (fun _ _ => Nat.zero_le _) hj
    exact Finset.mem_Icc.2 ⟨hT j hj, h1⟩
  · rintro ⟨J, T, hTJ, hs⟩
    exact ⟨T, fun j hj => (Finset.mem_Icc.1 (hTJ hj)).1, hs⟩

/-- Theorem `thm:leading`, final statement: `a = 2^r + r - 2` with `r ≥ 1` is not in `𝓐`. -/
theorem amem_gap {a r : ℕ} (hr : 1 ≤ r) (ha : a + 3 = 2 ^ r + r + 1) : ¬ Amem a := by
  intro h
  obtain ⟨J, hJ⟩ := (amem_iff_InE a).1 h
  obtain ⟨K, hK2, hKb, _⟩ := exists_top (by omega) hJ
  exact (beta_range (by omega : 3 ≤ a + 3)).1 ⟨K, hK2, hKb⟩ r hr ha

/-- Theorem `thm:leading`, final statement: otherwise there is a `K ≥ 2` with `β(K) = a + 3`. -/
theorem exists_candidate {a : ℕ} (ha : ∀ r, 1 ≤ r → a + 3 ≠ 2 ^ r + r + 1) :
    ∃ K, 2 ≤ K ∧ beta K = a + 3 :=
  (beta_range (by omega : 3 ≤ a + 3)).2 ha

/-- Theorem `thm:leading`, final statement: if `β(m+1) = a + 3`, then `a ∈ 𝓐` iff
`2^{m+1} (2^{h(m+1)} - (m+1)) ∈ 𝓔_m`. -/
theorem amem_iff_state {a m : ℕ} (hm : 1 ≤ m) (hb : beta (m + 1) = a + 3) :
    Amem a ↔ InE m (2 ^ (m + 1) * (2 ^ hfun (m + 1) - (m + 1))) := by
  rw [amem_iff_InE, ← hb]
  exact inE_two_pow_iff hm

/-! ### States and the recursion of Theorem `thm:step` -/

/-- A state `(J, w)`: `J ≥ 1` and `0 ≤ w ≤ J - 1`. -/
def IsState (J w : ℕ) : Prop := 1 ≤ J ∧ w + 1 ≤ J

/-- The state `(J, w)` is successful: `2^{J+1} w ∈ 𝓔_J`. -/
def Succ (J w : ℕ) : Prop := InE J (2 ^ (J + 1) * w)

theorem succ_zero (J : ℕ) : Succ J 0 := by
  unfold Succ
  rw [Nat.mul_zero]
  exact InE_zero J

/-- `s` is the least `σ ≥ 1` with `2^σ w + σ ≥ J + 1`. -/
def IsS (J w s : ℕ) : Prop :=
  1 ≤ s ∧ J + 1 ≤ 2 ^ s * w + s ∧ ∀ σ, 1 ≤ σ → σ < s → 2 ^ σ * w + σ < J + 1

/-- Existence of `s` and the bound `s ≤ J - 1` (Theorem `thm:step`). -/
theorem exists_S {J w : ℕ} (hst : IsState J w) (hw : 1 ≤ w) :
    ∃ s, IsS J w s ∧ s + 1 ≤ J := by
  classical
  obtain ⟨hJ, hwJ⟩ := hst
  have hJ1 : 1 ≤ J - 1 ∧ J + 1 ≤ 2 ^ (J - 1) * w + (J - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, J = m + 2 := ⟨J - 2, by omega⟩
    subst hm
    have e : m + 2 - 1 = m + 1 := by omega
    rw [e]
    have h2 : 2 ≤ 2 ^ (m + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 * 1 ≤ 2 ^ (m + 1) * w := Nat.mul_le_mul h2 hw
    constructor <;> omega
  have hex : ∃ σ, 1 ≤ σ ∧ J + 1 ≤ 2 ^ σ * w + σ := ⟨J - 1, hJ1⟩
  have hspec := Nat.find_spec hex
  have hle : Nat.find hex ≤ J - 1 := Nat.find_min' hex hJ1
  refine ⟨Nat.find hex, ⟨hspec.1, hspec.2, ?_⟩, by omega⟩
  intro σ h1 h2
  have h3 := Nat.find_min hex h2
  by_contra hc
  exact h3 ⟨h1, by omega⟩

theorem IsS_unique {J w s s' : ℕ} (h : IsS J w s) (h' : IsS J w s') : s = s' := by
  obtain ⟨a1, a2, a3⟩ := h
  obtain ⟨b1, b2, b3⟩ := h'
  rcases lt_trichotomy s s' with hlt | heq | hgt
  · have := b3 s a1 hlt
    omega
  · exact heq
  · have := a3 s' b1 hgt
    omega

/-- The terms `i 2^i` and the function `σ ↦ 2^σ w + σ`: for `σ + i = J + 1`,
`i 2^i ≤ 2^{J+1} w` iff `2^σ w + σ ≥ J + 1` (proof of Theorem `thm:step`). -/
theorem term_le_iff {σ i J w : ℕ} (hsum : σ + i = J + 1) :
    i * 2 ^ i ≤ 2 ^ (J + 1) * w ↔ J + 1 ≤ 2 ^ σ * w + σ := by
  have hp : 0 < 2 ^ i := by positivity
  have hJ : 2 ^ (J + 1) = 2 ^ σ * 2 ^ i := by rw [← pow_add, hsum]
  have e : 2 ^ σ * 2 ^ i * w = (2 ^ σ * w) * 2 ^ i := by ring
  have key : i * 2 ^ i ≤ 2 ^ (J + 1) * w ↔ i ≤ 2 ^ σ * w := by
    rw [hJ, e]
    constructor
    · intro h
      exact le_of_mul_le_mul_right h hp
    · intro h
      exact Nat.mul_le_mul_right _ h
  rw [key]
  constructor <;> intro h <;> omega

/-- The reduction step: if `2^s w = (m+1) + w'` and `s` is the least admissible integer for the state
`(m + s, w)`, then the state `(m + s, w)` is successful iff `2^{m+1} w' ∈ 𝓔_m`. -/
theorem succ_core {m s w w' : ℕ} (hS : IsS (m + s) w s) (hw' : 2 ^ s * w = (m + 1) + w') :
    Succ (m + s) w ↔ InE m (2 ^ (m + 1) * w') := by
  obtain ⟨hs1, hs2, hs3⟩ := hS
  have hV : 2 ^ (m + s + 1) * w = (m + 1) * 2 ^ (m + 1) + 2 ^ (m + 1) * w' := by
    have e1 : 2 ^ (m + s + 1) * w = 2 ^ (m + 1) * (2 ^ s * w) := by
      rw [show m + s + 1 = (m + 1) + s by ring, pow_add]
      ring
    rw [e1, hw']
    ring
  have hjV : (m + 1) * 2 ^ (m + 1) ≤ 2 ^ (m + s + 1) * w := by omega
  have hmax : ∀ i, m + 1 < i → i ≤ m + s → 2 ^ (m + s + 1) * w < i * 2 ^ i := by
    intro i hi hiJ
    by_contra hc
    push Not at hc
    have hsum : (m + s + 1 - i) + i = m + s + 1 := by omega
    have h1 := (term_le_iff (J := m + s) (w := w) hsum).1 hc
    have h2 := hs3 (m + s + 1 - i) (by omega) (by omega)
    omega
  have hg := greedy_iff (by omega : m + 1 ≤ m + s) hjV hmax
  have e : 2 ^ (m + s + 1) * w - (m + 1) * 2 ^ (m + 1) = 2 ^ (m + 1) * w' := by omega
  unfold Succ
  rw [hg, e]

/-- Theorem `thm:step` (2), written with `s = t + 1` and `J = m + (t + 1)`:
(a) if `2^t w + (t+1) = J + 1` the state is not successful; (b) otherwise
`w' = 2^{t+1} w + (t+1) - J - 1` gives a state `(m, w')` which is successful iff `(J, w)` is. -/
theorem step_main {m t w : ℕ} (hst : IsState (m + (t + 1)) w) (_hw : 1 ≤ w)
    (hS : IsS (m + (t + 1)) w (t + 1)) (hm : 1 ≤ m) :
    (2 ^ t * w + (t + 1) = m + (t + 1) + 1 → ¬ Succ (m + (t + 1)) w) ∧
    (2 ^ t * w + (t + 1) ≠ m + (t + 1) + 1 → ∃ w', 2 ^ (t + 1) * w = (m + 1) + w' ∧
      IsState m w' ∧ (Succ (m + (t + 1)) w ↔ Succ m w')) := by
  have hS' := hS
  obtain ⟨hs1, hs2, hs3⟩ := hS
  obtain ⟨w', hw'⟩ : ∃ w', 2 ^ (t + 1) * w = (m + 1) + w' :=
    ⟨2 ^ (t + 1) * w - (m + 1), by omega⟩
  have hcore := succ_core hS' hw'
  have hP : 2 ^ (t + 1) * w = 2 * (2 ^ t * w) := by ring
  constructor
  · intro hfail hsucc
    have h1 : w' = m + 1 := by omega
    rw [hcore, h1] at hsucc
    have h2 := InE_lt hsucc
    have e : 2 ^ (m + 1) * (m + 1) = (m + 1) * 2 ^ (m + 1) := by ring
    omega
  · intro hnf
    have hw'le : w' + 1 ≤ m := by
      rcases Nat.eq_zero_or_pos t with ht | ht
      · subst ht
        have h2 : 2 ^ (0 + 1) * w = 2 * w := by norm_num
        have h3 := hst.2
        omega
      · have h2 := hs3 t ht (by omega)
        omega
    exact ⟨w', hw', ⟨hm, hw'le⟩, hcore⟩

/-! ### The algorithm (Algorithm `alg:membership`, Corollary `cor:algo`) -/

/-- `Run n J w T`: the loop of Algorithm `alg:membership` started at the state `(J, w)` performs
exactly `n` iterations, never meets the failing case (2a), reaches a state with `w = 0`, and the
indices `j = J + 1 - s` produced form the set `T`. -/
inductive Run : ℕ → ℕ → ℕ → Finset ℕ → Prop
  | done {J : ℕ} (hJ : 1 ≤ J) : Run 0 J 0 ∅
  | step {m t w w' n : ℕ} {T : Finset ℕ} (hw : 1 ≤ w) (hS : IsS (m + (t + 1)) w (t + 1))
      (hm : 1 ≤ m) (hnf : 2 ^ t * w + (t + 1) ≠ m + (t + 1) + 1)
      (heq : 2 ^ (t + 1) * w = (m + 1) + w') (h : Run n m w' T) :
      Run (n + 1) (m + (t + 1)) w (insert (m + 1) T)

/-- Corollary `cor:algo`: a successful run represents `2^{J+1} w` by `T ⊆ {1, …, J}` and performs
at most `J - 1` iterations. -/
theorem run_sound {n J w : ℕ} {T : Finset ℕ} (h : Run n J w T) :
    1 ≤ J ∧ T ⊆ Finset.Icc 1 J ∧ ∑ j ∈ T, j * 2 ^ j = 2 ^ (J + 1) * w ∧ n + 1 ≤ J := by
  induction h with
  | @done J hJ =>
    exact ⟨hJ, Finset.empty_subset _, by simp, by omega⟩
  | @step m t w w' n T hw hS hm hnf heq h ih =>
    obtain ⟨hm1, hT', hsum', hn'⟩ := ih
    have hnot : m + 1 ∉ T := fun hx => by
      have := (Finset.mem_Icc.1 (hT' hx)).2
      omega
    refine ⟨by omega, ?_, ?_, by omega⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx'
      · exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
      · have h1 := Finset.mem_Icc.1 (hT' hx')
        exact Finset.mem_Icc.2 ⟨h1.1, by omega⟩
    · rw [Finset.sum_insert hnot, hsum']
      have e1 : 2 ^ (m + (t + 1) + 1) * w = 2 ^ (m + 1) * (2 ^ (t + 1) * w) := by
        rw [show m + (t + 1) + 1 = (m + 1) + (t + 1) by ring, pow_add]
        ring
      rw [e1, heq]
      ring

/-- Correctness of the algorithm: every successful state has a successful run. -/
theorem run_complete : ∀ (J w : ℕ), IsState J w → Succ J w → ∃ n T, Run n J w T := by
  intro J
  induction J using Nat.strong_induction_on with
  | _ J ih =>
    intro w hst hsucc
    rcases Nat.eq_zero_or_pos w with hw0 | hw
    · subst hw0
      exact ⟨0, ∅, Run.done hst.1⟩
    · obtain ⟨s, hS, hsJ⟩ := exists_S hst hw
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by have := hS.1; omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, J = m + (t + 1) := ⟨J - (t + 1), by omega⟩
      have hm : 1 ≤ m := by omega
      obtain ⟨hfail, hok⟩ := step_main hst hw hS hm
      by_cases hnf : 2 ^ t * w + (t + 1) = m + (t + 1) + 1
      · exact absurd hsucc (hfail hnf)
      · obtain ⟨w', heq, hst', hiff⟩ := hok hnf
        obtain ⟨n, T, hrun⟩ := ih m (by omega) w' hst' (hiff.1 hsucc)
        exact ⟨n + 1, insert (m + 1) T, Run.step hw hS hm hnf heq hrun⟩

/-- A state is successful iff the algorithm has a successful run from it. -/
theorem succ_iff_run {J w : ℕ} (hst : IsState J w) :
    Succ J w ↔ ∃ n T, Run n J w T := by
  constructor
  · exact run_complete J w hst
  · rintro ⟨n, T, h⟩
    obtain ⟨_, hT, hs, _⟩ := run_sound h
    exact ⟨T, hT, hs⟩

/-- Corollary `cor:algo`: the integer `2^s w + s` handled at each iteration is at most `2J + 2 ≤ 2K`. -/
theorem int_bound {J w s : ℕ} (hst : IsState J w) (_hw : 1 ≤ w) (hS : IsS J w s) :
    2 ^ s * w + s ≤ 2 * J + 2 := by
  obtain ⟨hs1, hs2, hs3⟩ := hS
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hP : 2 ^ (t + 1) * w = 2 * (2 ^ t * w) := by ring
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    have h2 : 2 ^ (0 + 1) * w = 2 * w := by norm_num
    have h3 := hst.2
    omega
  · have h2 := hs3 t ht (by omega)
    omega

/-! ### Lemma `lem:least` -/

theorem f_mono {w σ t : ℕ} (h : σ ≤ t) : 2 ^ σ * w + σ ≤ 2 ^ t * w + t :=
  Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) h)) h

theorem f_step {w t : ℕ} (_hw : 1 ≤ w) : 2 ^ t * w + t < 2 ^ (t + 1) * w + (t + 1) := by
  have hP : 2 ^ (t + 1) * w = 2 * (2 ^ t * w) := by ring
  omega

/-- Lemma `lem:least` (1): `s = t + 1` iff `f(t) ≤ J` and `f(t+1) ≥ J + 1`, where
`f(σ) = 2^σ w + σ`. -/
theorem least_char {J w t : ℕ} (hst : IsState J w) (_hw : 1 ≤ w) :
    IsS J w (t + 1) ↔ 2 ^ t * w + t ≤ J ∧ J + 1 ≤ 2 ^ (t + 1) * w + (t + 1) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h2⟩
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht
      have := hst.2
      simp only [pow_zero, one_mul]
      omega
    · have := h3 t ht (by omega)
      omega
  · rintro ⟨h1, h2⟩
    refine ⟨by omega, h2, ?_⟩
    intro σ hσ1 hσ2
    have := f_mono (w := w) (σ := σ) (t := t) (by omega)
    omega

/-- A state `(J, w)` with `w ≥ 1` fails: case (2a) of Theorem `thm:step`. -/
def Fails (J w : ℕ) : Prop := ∃ t, IsS J w (t + 1) ∧ 2 ^ t * w + (t + 1) = J + 1

/-- Lemma `lem:least` (3): `(J, w)` fails iff `2^{σ-1} w + σ = J + 1` for some `σ ≥ 2`. -/
theorem fails_iff {J w : ℕ} (hst : IsState J w) (hw : 1 ≤ w) :
    Fails J w ↔ ∃ t, 1 ≤ t ∧ 2 ^ t * w + (t + 1) = J + 1 := by
  constructor
  · rintro ⟨t, _, h⟩
    refine ⟨t, ?_, h⟩
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht
      have h3 := hst.2
      simp only [pow_zero, one_mul] at h
      omega
    · exact ht
  · rintro ⟨t, ht, h⟩
    have hP : 2 ^ (t + 1) * w = 2 * (2 ^ t * w) := by ring
    refine ⟨t, (least_char hst hw).2 ⟨by omega, by omega⟩, h⟩

/-- Lemma `lem:least` (2): if `2^σ w + σ = J + 1`, then `s = σ` and the state does not fail
(and `w' = 0`). -/
theorem least_two {J w t : ℕ} (hst : IsState J w) (hw : 1 ≤ w)
    (h : 2 ^ (t + 1) * w + (t + 1) = J + 1) :
    IsS J w (t + 1) ∧ 2 ^ t * w + (t + 1) ≠ J + 1 := by
  have hs := f_step (w := w) (t := t) hw
  refine ⟨(least_char hst hw).2 ⟨by omega, by omega⟩, ?_⟩
  have hP : 2 ^ (t + 1) * w = 2 * (2 ^ t * w) := by ring
  have hpos : 0 < 2 ^ t := by positivity
  have : 1 * 1 ≤ 2 ^ t * w := Nat.mul_le_mul hpos hw
  omega

/-- Lemma `lem:least` (3), first part: if `σ ≥ 2` and `2^{σ-1} w + σ = J + 1` then `s = σ`
(and the state fails). -/
theorem least_three {J w t : ℕ} (hst : IsState J w) (hw : 1 ≤ w) (_ht : 1 ≤ t)
    (h : 2 ^ t * w + (t + 1) = J + 1) : IsS J w (t + 1) :=
  (least_char hst hw).2 ⟨by omega, by
    have hP : 2 ^ (t + 1) * w = 2 * (2 ^ t * w) := by ring
    omega⟩

end SequenceNicolas.Recursion
