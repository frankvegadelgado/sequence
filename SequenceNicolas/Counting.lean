module

public import Mathlib
public import SequenceNicolas.Core
public import SequenceNicolas.Recursion
public import SequenceNicolas.Families

@[expose] public section

/-!
# The combinatorial side of the counting bounds

`A(n)` and `B(n)` are the counting functions of equation `eq:Adef`, for natural `n`.
The exponents `a = K + h(K) - 3` produced by Theorems `thm:members` and `thm:nonmembers` are
indexed by the candidate `K`; the sets `KA H` and `KB H` collect the candidates with `h(K) ≤ H`
whose exponent is, respectively is not, in `𝓐`.  The estimates of Theorem `thm:counting` follow
from injections of the index sets of the families into these sets.
-/

namespace SequenceNicolas.Counting

open SequenceNicolas.Recursion SequenceNicolas.Families

open scoped Classical

/-- `A(n) = #{a ∈ 𝓐 : a ≤ n}`. -/
noncomputable def Acount (n : ℕ) : ℕ := ((Finset.range (n + 1)).filter (fun a => Amem a)).card

/-- `B(n) = #{0 ≤ a ≤ n : a ∉ 𝓐}`. -/
noncomputable def Bcount (n : ℕ) : ℕ := ((Finset.range (n + 1)).filter (fun a => ¬ Amem a)).card

/-- Candidates `K` with `h(K) ≤ H` whose exponent `K + h(K) - 3` belongs to `𝓐`. -/
noncomputable def KA (H : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ H + 1)).filter (fun K => 2 ≤ K ∧ hfun K ≤ H ∧ Amem (K + hfun K - 3))

/-- Candidates `K` with `h(K) ≤ H` whose exponent `K + h(K) - 3` does not belong to `𝓐`. -/
noncomputable def KB (H : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ H + 1)).filter (fun K => 2 ≤ K ∧ hfun K ≤ H ∧ ¬ Amem (K + hfun K - 3))

theorem card_union_disj {s t : Finset ℕ} (h : Disjoint s t) : (s ∪ t).card = s.card + t.card := by
  exact Finset.card_union_of_disjoint h

theorem hfun_pos {K : ℕ} (hK : 2 ≤ K) : 1 ≤ hfun K := by
  by_contra hc
  have h0 : hfun K = 0 := by omega
  have := hfun_ge K
  rw [h0] at this
  simp at this
  omega

theorem mem_KA {H K : ℕ} : K ∈ KA H ↔ 2 ≤ K ∧ hfun K ≤ H ∧ Amem (K + hfun K - 3) := by
  unfold KA
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h1, h2, h3⟩
    have hK := hfun_ge K
    have hp : 2 ^ hfun K ≤ 2 ^ H := Nat.pow_le_pow_right (by norm_num) h2
    omega

theorem mem_KB {H K : ℕ} : K ∈ KB H ↔ 2 ≤ K ∧ hfun K ≤ H ∧ ¬ Amem (K + hfun K - 3) := by
  unfold KB
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h1, h2, h3⟩
    have hK := hfun_ge K
    have hp : 2 ^ hfun K ≤ 2 ^ H := Nat.pow_le_pow_right (by norm_num) h2
    omega

theorem exp_bound {H K n : ℕ} (hn : 2 ^ (H + 1) ≤ n) (h2 : hfun K ≤ H) :
    K + hfun K - 3 ≤ n := by
  have hK := hfun_ge K
  have hp : 2 ^ hfun K ≤ 2 ^ H := Nat.pow_le_pow_right (by norm_num) h2
  have hH := nat_lt_two_pow H
  have e : 2 ^ (H + 1) = 2 * 2 ^ H := by ring
  omega

theorem beta_eq_of_exp {K K' : ℕ} (hK : 2 ≤ K) (hK' : 2 ≤ K')
    (h : K + hfun K - 3 = K' + hfun K' - 3) : K = K' := by
  have h1 := hfun_pos hK
  have h2 := hfun_pos hK'
  exact beta_inj (by unfold beta; omega)

/-- `A(n) ≥ #KA(H)` when `2^{H+1} ≤ n`. -/
theorem KA_le {n H : ℕ} (hn : 2 ^ (H + 1) ≤ n) : (KA H).card ≤ Acount n := by
  unfold Acount
  apply Finset.card_le_card_of_injOn (fun K => K + hfun K - 3)
  · intro K hK
    have hK' : K ∈ KA H := hK
    obtain ⟨h1, h2, h3⟩ := mem_KA.1 hK'
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := exp_bound hn h2 (K := K); omega, h3⟩
  · intro K1 hK1 K2 hK2 heq
    have hK1' : K1 ∈ KA H := hK1
    have hK2' : K2 ∈ KA H := hK2
    obtain ⟨a1, _, _⟩ := mem_KA.1 hK1'
    obtain ⟨a2, _, _⟩ := mem_KA.1 hK2'
    have heq' : K1 + hfun K1 - 3 = K2 + hfun K2 - 3 := heq
    exact beta_eq_of_exp a1 a2 heq'

theorem nc_inj {r r' : ℕ} (hr : 1 ≤ r) (hr' : 1 ≤ r') (h : 2 ^ r + r - 2 = 2 ^ r' + r' - 2) :
    r = r' := by
  have h1 : 2 ≤ 2 ^ r := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  have h2 : 2 ≤ 2 ^ r' := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r' := Nat.pow_le_pow_right (by norm_num) hr'
  rcases lt_trichotomy r r' with hlt | heq | hgt
  · have : 2 ^ r < 2 ^ r' := by
      exact Nat.pow_lt_pow_right (by norm_num) hlt
    omega
  · exact heq
  · have : 2 ^ r' < 2 ^ r := by
      exact Nat.pow_lt_pow_right (by norm_num) hgt
    omega

/-- `B(n) ≥ #KB(H) + H` when `2^{H+1} ≤ n`: the exponents `2^r + r - 2`, `1 ≤ r ≤ H`, have no
candidate (Theorem `thm:leading`). -/
theorem KB_le {n H : ℕ} (hn : 2 ^ (H + 1) ≤ n) : (KB H).card + H ≤ Bcount n := by
  have hS1 : ((KB H).image (fun K => K + hfun K - 3)).card = (KB H).card := by
    apply Finset.card_image_of_injOn
    intro K1 hK1 K2 hK2 heq
    have hK1' : K1 ∈ KB H := hK1
    have hK2' : K2 ∈ KB H := hK2
    obtain ⟨a1, _, _⟩ := mem_KB.1 hK1'
    obtain ⟨a2, _, _⟩ := mem_KB.1 hK2'
    have heq' : K1 + hfun K1 - 3 = K2 + hfun K2 - 3 := heq
    exact beta_eq_of_exp a1 a2 heq'
  have hS2 : ((Finset.Icc 1 H).image (fun r => 2 ^ r + r - 2)).card = H := by
    rw [Finset.card_image_of_injOn, Nat.card_Icc]
    · omega
    · intro r hr r' hr' heq
      have h1 := (Finset.mem_Icc.1 hr).1
      have h2 := (Finset.mem_Icc.1 hr').1
      exact nc_inj h1 h2 heq
  have hdisj : Disjoint ((KB H).image (fun K => K + hfun K - 3))
      ((Finset.Icc 1 H).image (fun r => 2 ^ r + r - 2)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨K, hK, hKx⟩ := Finset.mem_image.1 hx1
    obtain ⟨r, hr, hrx⟩ := Finset.mem_image.1 hx2
    obtain ⟨a1, _, _⟩ := mem_KB.1 hK
    have hr1 := (Finset.mem_Icc.1 hr).1
    have h1 := hfun_pos a1
    have h2 : 2 ≤ 2 ^ r := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr1
    have hb : 3 ≤ x + 3 := by omega
    have := (beta_range hb).1 ⟨K, a1, by unfold beta; omega⟩ r hr1
    omega
  have hsub : ((KB H).image (fun K => K + hfun K - 3)) ∪
      ((Finset.Icc 1 H).image (fun r => 2 ^ r + r - 2)) ⊆
      (Finset.range (n + 1)).filter (fun a => ¬ Amem a) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases Finset.mem_union.1 hx with hx | hx
    · obtain ⟨K, hK, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨a1, a2, a3⟩ := mem_KB.1 hK
      exact ⟨by have := exp_bound hn a2 (K := K); omega, a3⟩
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.1 hr
      have h2 : 2 ≤ 2 ^ r := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr1
      have hp : 2 ^ r ≤ 2 ^ H := Nat.pow_le_pow_right (by norm_num) hr2
      have hH := nat_lt_two_pow H
      have e : 2 ^ (H + 1) = 2 * 2 ^ H := by ring
      refine ⟨by omega, ?_⟩
      exact amem_gap hr1 (by omega)
  have := Finset.card_le_card hsub
  rw [card_union_disj hdisj, hS1, hS2] at this
  unfold Bcount
  exact this

/-! ### Exponents from the equation `K (2^m + 1) = 2^{h+m} + e` -/

theorem eqn_mono {m m' e e' h K K' : ℕ} (hlt : m < m') (he : e < e')
    (hK : K * (2 ^ m + 1) = 2 ^ (h + m) + e) (hK' : K' * (2 ^ m' + 1) = 2 ^ (h + m') + e')
    (hl : K < 2 ^ h) (hl' : K' < 2 ^ h) : K < K' := by
  obtain ⟨D, hD⟩ : ∃ D, 2 ^ h = K + D := ⟨2 ^ h - K, by omega⟩
  obtain ⟨D', hD'⟩ : ∃ D', 2 ^ h = K' + D' := ⟨2 ^ h - K', by omega⟩
  have hP : 2 ^ m < 2 ^ m' := by
    exact Nat.pow_lt_pow_right (by norm_num) hlt
  have e1 : 2 ^ (h + m) = (K + D) * 2 ^ m := by rw [pow_add, hD]
  have e2 : 2 ^ (h + m') = (K' + D') * 2 ^ m' := by rw [pow_add, hD']
  rw [e1] at hK
  rw [e2] at hK'
  have h1 : K = D * 2 ^ m + e := by nlinarith [hK]
  have h2 : K' = D' * 2 ^ m' + e' := by nlinarith [hK']
  by_contra hc
  push Not at hc
  have hDD : D ≤ D' := by omega
  have m1 : D * 2 ^ m ≤ D' * 2 ^ m := Nat.mul_le_mul_right _ hDD
  have m2 : D' * 2 ^ m ≤ D' * 2 ^ m' := Nat.mul_le_mul_left _ hP.le
  omega

theorem eqn_inj {m m' e e' h K : ℕ} (hme : m < m' → e < e') (hme' : m' < m → e' < e)
    (hK : K * (2 ^ m + 1) = 2 ^ (h + m) + e) (hK' : K * (2 ^ m' + 1) = 2 ^ (h + m') + e')
    (hl : K < 2 ^ h) : m = m' := by
  rcases lt_trichotomy m m' with h1 | h1 | h1
  · exact absurd (eqn_mono h1 (hme h1) hK hK' hl hl) (lt_irrefl K)
  · exact h1
  · exact absurd (eqn_mono h1 (hme' h1) hK' hK hl hl) (lt_irrefl K)

theorem amem_of_eight {n e : ℕ} (he : 3 ≤ e) (h : 8 * SequenceNicolas.Core.c n = 2 ^ e) :
    Amem (e - 3) := by
  obtain ⟨x, hx⟩ : ∃ x, e = x + 3 := ⟨e - 3, by omega⟩
  have e3 : e - 3 = x := by omega
  rw [e3]
  unfold Amem
  refine ⟨n, ?_⟩
  rw [hx, pow_add] at h
  omega

/-! ### The members of Theorem `thm:members` -/

/-- `K = (2^{h+s} + s)/(2^s + 1)` with `s = 2^k` and `h = k + 2^{k+1} t`. -/
noncomputable def Kmem (k t : ℕ) : ℕ :=
  (2 ^ ((k + 2 ^ (k + 1) * t) + 2 ^ k) + 2 ^ k) / (2 ^ (2 ^ k) + 1)

theorem Kmem_spec {k t : ℕ} (ht : 1 ≤ t) :
    Kmem k t * (2 ^ (2 ^ k) + 1) = 2 ^ ((k + 2 ^ (k + 1) * t) + 2 ^ k) + 2 ^ k ∧
    Kmem k t < 2 ^ (k + 2 ^ (k + 1) * t) ∧ 2 ^ (k + 2 ^ (k + 1) * t) < 2 * Kmem k t ∧
    2 ≤ Kmem k t ∧ hfun (Kmem k t) = k + 2 ^ (k + 1) * t ∧
    Amem (Kmem k t + (k + 2 ^ (k + 1) * t) - 3) := by
  obtain ⟨s, hs⟩ : ∃ s, s = 2 ^ k := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h, h = k + 2 ^ (k + 1) * t := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by
    have : 0 < 2 ^ k := by positivity
    omega
  have hp : 2 ^ (k + 1) = 2 * s := by rw [hs]; ring
  have hh2 : h = k + 2 * s * t := by rw [hh, hp]
  have hkh : k + 2 ≤ h := by
    have : 2 * s * 1 ≤ 2 * s * t := Nat.mul_le_mul_left _ ht
    omega
  have hmod : 2 ^ h ≡ s [MOD 2 ^ s + 1] := by
    have h1 := (pow_period s t).mul_left (2 ^ k)
    rw [mul_one, ← pow_add, ← hs] at h1
    rw [hh2]
    exact h1
  obtain ⟨K, hK⟩ := dvd_of_modeq hmod
  have hKeq : K * (2 ^ s + 1) = 2 ^ (h + s) + s := by
    rw [Nat.mul_comm]
    exact hK.symm
  have hlt : s < 2 ^ h := by
    rw [hs]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨hKl, hKr⟩ := SequenceNicolas.Core.members_two_bounds hs1 hlt hKeq
  have h4 : 2 ^ (k + 2) ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hkh
  have e4 : 2 ^ (k + 2) = 4 * s := by rw [hs]; ring
  have hKs : s + 2 ≤ K := by omega
  have hK2 : 2 ≤ K := by omega
  have hfK : hfun K = h := hfun_of_bounds hK2 hKl.le hKr
  have hdiv : Kmem k t = K := by
    unfold Kmem
    rw [← hh, ← hs]
    exact Nat.div_eq_of_eq_mul_left (by positivity) hKeq.symm
  rw [hdiv, ← hh, ← hs]
  refine ⟨hKeq, hKl, hKr, hK2, hfK, ?_⟩
  have h8 := SequenceNicolas.Core.members_two hs1 hKs hKeq
  exact amem_of_eight (by omega) h8

/-- Theorem `thm:members` (1): `2^h`, `h ≥ 1`, has `h(2^h) = h` and the exponent `2^h + h - 3`
lies in `𝓐`. -/
theorem M1_spec {h : ℕ} (hh : 1 ≤ h) :
    2 ≤ 2 ^ h ∧ hfun (2 ^ h) = h ∧ Amem (2 ^ h + h - 3) := by
  have h2 : 2 ≤ 2 ^ h := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
  have hf : hfun (2 ^ h) = h := hfun_of_bounds h2 (le_refl _) (by omega)
  refine ⟨h2, hf, ?_⟩
  have h8 := SequenceNicolas.Core.members_one h hh
  exact amem_of_eight (by omega) h8

/-- The index set of the members `(k, t)`, `0 ≤ k ≤ κ`, `1 ≤ t ≤ ⌊(H - k)/2^{k+1}⌋`. -/
noncomputable def idxM (H κ : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.range (κ + 1)).sigma (fun k => Finset.Icc 1 ((H - k) / 2 ^ (k + 1)))

theorem card_idxM (H κ : ℕ) :
    (idxM H κ).card = ∑ k ∈ Finset.range (κ + 1), (H - k) / 2 ^ (k + 1) := by
  unfold idxM
  rw [Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.card_Icc]
  exact Nat.add_sub_cancel _ _

theorem idxM_mem {H κ k t : ℕ} (hκ : κ ≤ H) (hp : (⟨k, t⟩ : Σ _ : ℕ, ℕ) ∈ idxM H κ) :
    1 ≤ t ∧ k + 2 ^ (k + 1) * t ≤ H := by
  unfold idxM at hp
  simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hp
  obtain ⟨hk, ht1, ht2⟩ := hp
  have hpos : 0 < 2 ^ (k + 1) := by positivity
  have h1 : t * 2 ^ (k + 1) ≤ H - k := (Nat.le_div_iff_mul_le hpos).1 ht2
  have h2 : 2 ^ (k + 1) * t = t * 2 ^ (k + 1) := Nat.mul_comm _ _
  refine ⟨ht1, ?_⟩
  omega

theorem Kmem_inj {k t k' t' : ℕ} (ht : 1 ≤ t) (ht' : 1 ≤ t')
    (heq : Kmem k t = Kmem k' t') : k = k' ∧ t = t' := by
  obtain ⟨e1, l1, r1, k1, f1, _⟩ := Kmem_spec (k := k) ht
  obtain ⟨e2, l2, r2, k2, f2, _⟩ := Kmem_spec (k := k') ht'
  have hh : k + 2 ^ (k + 1) * t = k' + 2 ^ (k' + 1) * t' := by
    have a := f1
    rw [heq] at a
    omega
  rw [← heq] at e2
  have hm : 2 ^ k = 2 ^ k' := by
    apply eqn_inj (m := 2 ^ k) (m' := 2 ^ k') (e := 2 ^ k) (e' := 2 ^ k') (h := k + 2 ^ (k + 1) * t)
        (K := Kmem k t) (by intro h; exact h) (by intro h; exact h) e1 _ l1
    rw [hh]
    exact e2
  have hkk : k = k' := Nat.pow_right_injective (le_refl 2) hm
  subst hkk
  refine ⟨rfl, ?_⟩
  have hpos : 0 < 2 ^ (k + 1) := by positivity
  exact Nat.eq_of_mul_eq_mul_left hpos (by omega)

/-- `K (Q + 1) = P Q + c` with `Q ≥ 2` and `c > 0` forces `3 K > 2 P`: such candidates lie above
`2/3` of `P = 2^h`. -/
theorem sep_gen {K P Q c : ℕ} (hQ : 2 ≤ Q) (hc : 0 < c) (h : K * (Q + 1) = P * Q + c) :
    2 * P < 3 * K := by
  by_contra hcon
  push Not at hcon
  have h1 : 3 * K * (Q + 1) ≤ 2 * P * (Q + 1) := Nat.mul_le_mul_right _ hcon
  have h2 : P * 2 ≤ P * Q := Nat.mul_le_mul_left P hQ
  nlinarith [h1, h2, h]

theorem Kmem_sep {k t : ℕ} (ht : 1 ≤ t) :
    2 * 2 ^ (k + 2 ^ (k + 1) * t) < 3 * Kmem k t := by
  obtain ⟨e1, _⟩ := Kmem_spec (k := k) ht
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hQ : 2 ≤ 2 ^ (2 ^ k) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right (by norm_num) hk
  have e2 : 2 ^ ((k + 2 ^ (k + 1) * t) + 2 ^ k) = 2 ^ (k + 2 ^ (k + 1) * t) * 2 ^ (2 ^ k) :=
    pow_add _ _ _
  rw [e2] at e1
  exact sep_gen hQ (by positivity) e1

/-- The members of Theorem `thm:members`: `2^h`, `1 ≤ h ≤ H`, and the candidates `(k, t)`. -/
noncomputable def Mset (H κ : ℕ) : Finset ℕ :=
  (Finset.Icc 1 H).image (fun h => 2 ^ h) ∪
    (idxM H κ).image (fun p : Σ _ : ℕ, ℕ => Kmem p.1 p.2)

theorem Mset_prop {H κ x : ℕ} (hκ : κ ≤ H) (hx : x ∈ Mset H κ) :
    x ∈ KA H ∧ 2 * 2 ^ hfun x < 3 * x := by
  unfold Mset at hx
  rcases Finset.mem_union.1 hx with hx | hx
  · obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨hh1, hh2⟩ := Finset.mem_Icc.1 hh
    obtain ⟨a1, a2, a3⟩ := M1_spec hh1
    refine ⟨?_, ?_⟩
    · rw [mem_KA]
      refine ⟨a1, by omega, ?_⟩
      rw [a2]
      exact a3
    · rw [a2]
      have : 0 < 2 ^ h := by positivity
      omega
  · obtain ⟨⟨k, t⟩, hp, rfl⟩ := Finset.mem_image.1 hx
    have a := idxM_mem hκ hp
    obtain ⟨_, _, _, k1, f1, hA⟩ := Kmem_spec (k := k) a.1
    refine ⟨?_, ?_⟩
    · rw [mem_KA]
      refine ⟨k1, ?_, ?_⟩
      · show hfun (Kmem k t) ≤ H
        omega
      show Amem (Kmem k t + hfun (Kmem k t) - 3)
      rw [f1]
      exact hA
    · show 2 * 2 ^ hfun (Kmem k t) < 3 * Kmem k t
      rw [f1]
      exact Kmem_sep a.1

theorem Mset_card {H κ : ℕ} (hκ : κ ≤ H) :
    (Mset H κ).card = H + ∑ k ∈ Finset.range (κ + 1), (H - k) / 2 ^ (k + 1) := by
  have hM1 : ((Finset.Icc 1 H).image (fun h => 2 ^ h)).card = H := by
    rw [Finset.card_image_of_injOn, Nat.card_Icc]
    · omega
    · intro a _ b _ hab
      exact Nat.pow_right_injective (le_refl 2) hab
  have hM2 : ((idxM H κ).image (fun p : Σ _ : ℕ, ℕ => Kmem p.1 p.2)).card = (idxM H κ).card := by
    apply Finset.card_image_of_injOn
    rintro ⟨k, t⟩ hp ⟨k', t'⟩ hp' heq
    have a := idxM_mem hκ hp
    have b := idxM_mem hκ hp'
    obtain ⟨hk, ht⟩ := Kmem_inj a.1 b.1 heq
    subst hk
    subst ht
    rfl
  have hdisj : Disjoint ((Finset.Icc 1 H).image (fun h => 2 ^ h))
      ((idxM H κ).image (fun p : Σ _ : ℕ, ℕ => Kmem p.1 p.2)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨h, hh, hhx⟩ := Finset.mem_image.1 hx1
    obtain ⟨⟨k, t⟩, hp, hpx⟩ := Finset.mem_image.1 hx2
    have a := idxM_mem hκ hp
    have hh1 := (Finset.mem_Icc.1 hh).1
    obtain ⟨_, l1, _, _, f1, _⟩ := Kmem_spec (k := k) a.1
    obtain ⟨_, hf, _⟩ := M1_spec hh1
    have hpx' : Kmem k t = 2 ^ h := hpx.trans hhx.symm
    rw [hpx', hf] at f1
    rw [hpx', f1] at l1
    omega
  unfold Mset
  rw [card_union_disj hdisj, hM1, hM2, card_idxM]

theorem A_nat {n H κ : ℕ} (hn : 2 ^ (H + 1) ≤ n) (hκ : κ ≤ H) :
    H + ∑ k ∈ Finset.range (κ + 1), (H - k) / 2 ^ (k + 1) ≤ Acount n := by
  have hsub : Mset H κ ⊆ KA H := fun x hx => (Mset_prop hκ hx).1
  have h1 := Finset.card_le_card hsub
  rw [Mset_card hκ] at h1
  have h2 := KA_le hn
  omega

end SequenceNicolas.Counting
