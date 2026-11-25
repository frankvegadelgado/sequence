module

public import Mathlib
public import SequenceNicolas.Counting
public import SequenceNicolas.CountingB
public import SequenceNicolas.SymFamilies

@[expose] public section

/-!
# Theorem `thm:counting2`: the combinatorial side

The families of Theorem `thm:symfamilies` add three index sets to those of Theorem `thm:counting`.
All their candidates `K` satisfy `3K < 2·2^{h(K)}`, whereas the candidates of Theorems
`thm:members` and `thm:nonmembers` satisfy `3K > 2·2^{h(K)}`; this separates the two groups.
-/

namespace SequenceNicolas.Counting

open SequenceNicolas.Recursion SequenceNicolas.Families SequenceNicolas.SymFamilies

open scoped Classical

/-- `w = (2^h - e)/(2^m - 1)`. -/
def Ws (m e h : ℕ) : ℕ := (2 ^ h - e) / (2 ^ m - 1)

/-- `K = (2^h + w + 2)/2` (`K = 2^{h-1} + 1 + w/2`). -/
def Ks (m e h : ℕ) : ℕ := (2 ^ h + Ws m e h + 2) / 2

theorem Ks_eq {m e h w K : ℕ} (hm : 1 ≤ m) (hw : w * (2 ^ m - 1) + e = 2 ^ h)
    (hK : 2 * K = 2 ^ h + w + 2) : Ks m e h = K := by
  have h2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hpos : 0 < 2 ^ m - 1 := by omega
  have hW : Ws m e h = w := by
    unfold Ws
    exact Nat.div_eq_of_eq_mul_left hpos (by omega)
  unfold Ks
  rw [hW]
  omega

/-- The data of one symmetric family. -/
abbrev SymOK (m e h w K : ℕ) : Prop :=
  w * (2 ^ m - 1) + e = 2 ^ h ∧ 2 * K = 2 ^ h + w + 2 ∧ 2 ^ (h - 1) + 1 < K ∧ K < 2 ^ h

theorem symok_hfun {m e h w K : ℕ} (hh : 4 ≤ h) (hs : SymOK m e h w K) :
    2 ≤ K ∧ hfun K = h := by
  obtain ⟨_, h2, h3, h4⟩ := hs
  have h16 : 2 ^ 4 ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
  have e16 : (2 : ℕ) ^ 4 = 16 := by norm_num
  have hK : 2 ≤ K := by omega
  exact ⟨hK, hfun_of_bounds hK h4.le (by omega)⟩

theorem symok_sep {m e h w K : ℕ} (hm : 3 ≤ m) (hh : 4 ≤ h) (hs : SymOK m e h w K) :
    3 * K < 2 * 2 ^ h := by
  obtain ⟨h1, h2, _, _⟩ := hs
  have h16 : 2 ^ 4 ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
  have h8 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have e16 : (2 : ℕ) ^ 4 = 16 := by norm_num
  have e8 : (2 : ℕ) ^ 3 = 8 := by norm_num
  have h7 : 7 ≤ 2 ^ m - 1 := by omega
  have h9 : w * 7 ≤ w * (2 ^ m - 1) := Nat.mul_le_mul_left w h7
  omega

theorem symok_inj {m e h w K m' e' h' w' K' : ℕ} (h4 : 4 ≤ h) (h4' : 4 ≤ h')
    (hs : SymOK m e h w K) (hs' : SymOK m' e' h' w' K') (hK : K = K')
    (hme : m < m' → e < e') (hme' : m' < m → e' < e) : m = m' ∧ h = h' := by
  obtain ⟨_, f1⟩ := symok_hfun h4 hs
  obtain ⟨_, f2⟩ := symok_hfun h4' hs'
  have hh : h = h' := by
    rw [hK] at f1
    omega
  subst hh
  refine ⟨?_, rfl⟩
  obtain ⟨a1, a2, _, _⟩ := hs
  obtain ⟨b1, b2, _, _⟩ := hs'
  subst hK
  have hw : w = w' := by omega
  subst hw
  rcases lt_trichotomy m m' with hl | he | hg
  · have hp : 2 ^ m ≤ 2 ^ m' := Nat.pow_le_pow_right (by norm_num) hl.le
    have : w * (2 ^ m - 1) ≤ w * (2 ^ m' - 1) := Nat.mul_le_mul_left w (by omega)
    have := hme hl
    omega
  · exact he
  · have hp : 2 ^ m' ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hg.le
    have : w * (2 ^ m' - 1) ≤ w * (2 ^ m - 1) := Nat.mul_le_mul_left w (by omega)
    have := hme' hg
    omega

/-! ### The family (1): `K = 2^{h-1} + 1` -/

theorem sym1_spec {h : ℕ} (hh : 4 ≤ h) :
    2 ≤ 2 ^ (h - 1) + 1 ∧ hfun (2 ^ (h - 1) + 1) = h ∧ Amem (2 ^ (h - 1) + 1 + h - 3) ∧
      3 * (2 ^ (h - 1) + 1) < 2 * 2 ^ h := by
  obtain ⟨r, rfl⟩ : ∃ r, h = r + 1 := ⟨h - 1, by omega⟩
  have e : r + 1 - 1 = r := by omega
  rw [e]
  obtain ⟨_, hA, hb⟩ := symfam_one r
  have hr : 3 ≤ r := by omega
  have h8 : 2 ^ 3 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  have e8 : (2 : ℕ) ^ 3 = 8 := by norm_num
  have e2 : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
  have hr1 : r < 2 ^ r := nat_lt_two_pow r
  have hf : hfun (2 ^ r + 1) = r + 1 := by
    unfold beta at hb
    omega
  refine ⟨by omega, hf, ?_, by omega⟩
  have : 2 ^ r + 1 + (r + 1) - 3 = 2 ^ r + r - 1 := by omega
  rw [this]
  exact hA

/-! ### The family (2) -/

/-- The index `(j, q)` stands for `i = j + 1`, `σ = 2^j + 1`, `h = i + (σ + 1) q`. -/
noncomputable def idxS2 (H κ : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.range κ).sigma (fun j => Finset.Icc 1 ((H - (j + 1)) / (2 ^ j + 1 + 1)))

def hS2 (j q : ℕ) : ℕ := (j + 1) + (2 ^ j + 1 + 1) * q

def fS2 (p : Σ _ : ℕ, ℕ) : ℕ := Ks (2 ^ p.1 + 1 + 1) (2 * (2 ^ p.1 + 1) - 2) (hS2 p.1 p.2)

theorem card_idxS2 (H κ : ℕ) :
    (idxS2 H κ).card = ∑ j ∈ Finset.range κ, (H - (j + 1)) / (2 ^ j + 1 + 1) := by
  unfold idxS2
  rw [Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.card_Icc]
  exact Nat.add_sub_cancel _ _

theorem idxS2_mem {H κ j q : ℕ} (hκ : κ ≤ H) (hp : (⟨j, q⟩ : Σ _ : ℕ, ℕ) ∈ idxS2 H κ) :
    1 ≤ q ∧ hS2 j q ≤ H := by
  unfold idxS2 at hp
  simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hp
  obtain ⟨hj, hq1, hq2⟩ := hp
  have hpos : 0 < 2 ^ j + 1 + 1 := by positivity
  have h1 : q * (2 ^ j + 1 + 1) ≤ H - (j + 1) := (Nat.le_div_iff_mul_le hpos).1 hq2
  have h2 : (2 ^ j + 1 + 1) * q = q * (2 ^ j + 1 + 1) := Nat.mul_comm _ _
  refine ⟨hq1, ?_⟩
  unfold hS2
  omega

theorem S2_data {j q : ℕ} (hq : 1 ≤ q) :
    ∃ w, SymOK (2 ^ j + 1 + 1) (2 * (2 ^ j + 1) - 2) (hS2 j q) w (fS2 ⟨j, q⟩) ∧
      Amem (fS2 ⟨j, q⟩ + hS2 j q - 3) ∧ 4 ≤ hS2 j q := by
  have h1 : 2 ^ (j + 1 - 1) + 1 = 2 ^ j + 1 := by rw [Nat.add_sub_cancel]
  have hpos : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have hmul : 2 ^ j + 1 + 1 ≤ (2 ^ j + 1 + 1) * q := Nat.le_mul_of_pos_right _ hq
  have hh : 2 ^ j + 1 + 2 ≤ hS2 j q := by unfold hS2; omega
  have hmod : hS2 j q % (2 ^ j + 1 + 1) = (j + 1) % (2 ^ j + 1 + 1) := by
    unfold hS2
    exact Nat.add_mul_mod_self_left (j + 1) (2 ^ j + 1 + 1) q
  obtain ⟨w, K, a1, _, _, a4, a5, a6, a7⟩ :=
    symfam_two (i := j + 1) (σ := 2 ^ j + 1) (h := hS2 j q) (by omega) h1.symm hh hmod
  have hK := Ks_eq (m := 2 ^ j + 1 + 1) (e := 2 * (2 ^ j + 1) - 2) (h := hS2 j q) (w := w)
    (K := K) (by omega) a1 a4
  have hF : fS2 ⟨j, q⟩ = K := hK
  refine ⟨w, ?_, ?_, by omega⟩
  · rw [hF]
    exact ⟨a1, a4, a5, a6⟩
  · rw [hF]
    exact a7

/-! ### The family (3) -/

/-- The index `(j, q)` stands for `i = j + 2`, `σ = 2^{j+1} + 1`, `h = i + σ q`. -/
noncomputable def idxS3 (H κ : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.range (κ - 1)).sigma (fun j => Finset.Icc 1 ((H - (j + 2)) / (2 ^ (j + 1) + 1)))

def hS3 (j q : ℕ) : ℕ := (j + 2) + (2 ^ (j + 1) + 1) * q

def fS3 (p : Σ _ : ℕ, ℕ) : ℕ := Ks (2 ^ (p.1 + 1) + 1) (2 * (2 ^ (p.1 + 1) + 1) - 2) (hS3 p.1 p.2)

theorem card_idxS3 (H κ : ℕ) :
    (idxS3 H κ).card = ∑ j ∈ Finset.range (κ - 1), (H - (j + 2)) / (2 ^ (j + 1) + 1) := by
  unfold idxS3
  rw [Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.card_Icc]
  exact Nat.add_sub_cancel _ _

theorem idxS3_mem {H κ j q : ℕ} (hκ : κ ≤ H) (hp : (⟨j, q⟩ : Σ _ : ℕ, ℕ) ∈ idxS3 H κ) :
    1 ≤ q ∧ hS3 j q ≤ H := by
  unfold idxS3 at hp
  simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hp
  obtain ⟨hj, hq1, hq2⟩ := hp
  have hpos : 0 < 2 ^ (j + 1) + 1 := by positivity
  have h1 : q * (2 ^ (j + 1) + 1) ≤ H - (j + 2) := (Nat.le_div_iff_mul_le hpos).1 hq2
  have h2 : (2 ^ (j + 1) + 1) * q = q * (2 ^ (j + 1) + 1) := Nat.mul_comm _ _
  refine ⟨hq1, ?_⟩
  unfold hS3
  omega

theorem S3_data {j q : ℕ} (hq : 1 ≤ q) :
    ∃ w, SymOK (2 ^ (j + 1) + 1) (2 * (2 ^ (j + 1) + 1) - 2) (hS3 j q) w (fS3 ⟨j, q⟩) ∧
      ¬ Amem (fS3 ⟨j, q⟩ + hS3 j q - 3) ∧ 4 ≤ hS3 j q := by
  have h1 : 2 ^ (j + 2 - 1) + 1 = 2 ^ (j + 1) + 1 := by
    have : j + 2 - 1 = j + 1 := by omega
    rw [this]
  have hpos : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
  have hmul : 2 ^ (j + 1) + 1 ≤ (2 ^ (j + 1) + 1) * q := Nat.le_mul_of_pos_right _ hq
  have hh : 2 ^ (j + 1) + 1 + 1 ≤ hS3 j q := by unfold hS3; omega
  have hmod : hS3 j q % (2 ^ (j + 1) + 1) = (j + 2) % (2 ^ (j + 1) + 1) := by
    unfold hS3
    exact Nat.add_mul_mod_self_left (j + 2) (2 ^ (j + 1) + 1) q
  obtain ⟨w, K, a1, _, _, a4, a5, a6, a7⟩ :=
    symfam_three (i := j + 2) (σ := 2 ^ (j + 1) + 1) (h := hS3 j q) (by omega) h1.symm hh hmod
  have hK := Ks_eq (m := 2 ^ (j + 1) + 1) (e := 2 * (2 ^ (j + 1) + 1) - 2) (h := hS3 j q)
    (w := w) (K := K) (by omega) a1 a4
  have hF : fS3 ⟨j, q⟩ = K := hK
  have h4 : 4 ≤ hS3 j q := by
    have : 2 ≤ 2 ^ (j + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold hS3
    omega
  refine ⟨w, ?_, ?_, h4⟩
  · rw [hF]
    exact ⟨a1, a4, a5, a6⟩
  · rw [hF]
    exact a7

/-! ### The members: `A(n) ≥ |M| + (H - 3) + |S2|` -/

/-- Family (1) of Theorem `thm:symfamilies`. -/
noncomputable def Sym1 (H : ℕ) : Finset ℕ := (Finset.Icc 4 H).image (fun h => 2 ^ (h - 1) + 1)

noncomputable def Sym2 (H κ : ℕ) : Finset ℕ := (idxS2 H κ).image fS2

theorem sym_exp_mem {H K : ℕ} (hK : 2 ≤ K) (hf : hfun K ≤ H) (hA : Amem (K + hfun K - 3)) :
    K ∈ KA H := mem_KA.2 ⟨hK, hf, hA⟩

theorem Sym1_prop {H x : ℕ} (hx : x ∈ Sym1 H) :
    x ∈ KA H ∧ 3 * x < 2 * 2 ^ hfun x ∧ ∃ h, 4 ≤ h ∧ h ≤ H ∧ hfun x = h ∧ x = 2 ^ (h - 1) + 1 := by
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨hh1, hh2⟩ := Finset.mem_Icc.1 hh
  obtain ⟨a1, a2, a3, a4⟩ := sym1_spec hh1
  refine ⟨?_, ?_, h, hh1, hh2, a2, rfl⟩
  · apply sym_exp_mem a1 (by omega)
    rw [a2]
    exact a3
  · rw [a2]
    exact a4

theorem Sym2_prop {H κ x : ℕ} (hκ : κ ≤ H) (hx : x ∈ Sym2 H κ) :
    x ∈ KA H ∧ 3 * x < 2 * 2 ^ hfun x ∧
      ∃ h, 4 ≤ h ∧ h ≤ H ∧ hfun x = h ∧ 2 ^ (h - 1) + 1 < x := by
  obtain ⟨⟨j, q⟩, hp, rfl⟩ := Finset.mem_image.1 hx
  have a := idxS2_mem hκ hp
  obtain ⟨w, hs, hA, h4⟩ := S2_data (j := j) a.1
  obtain ⟨hK2, hf⟩ := symok_hfun h4 hs
  have hsep := symok_sep (by
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    omega) h4 hs
  refine ⟨?_, ?_, hS2 j q, h4, a.2, hf, hs.2.2.1⟩
  · apply sym_exp_mem hK2 (by rw [hf]; exact a.2)
    rw [hf]
    exact hA
  · rw [hf]
    exact hsep

theorem Sym2_card {H κ : ℕ} (hκ : κ ≤ H) : (Sym2 H κ).card = (idxS2 H κ).card := by
  unfold Sym2
  apply Finset.card_image_of_injOn
  rintro ⟨j, q⟩ hp ⟨j', q'⟩ hp' heq
  have a := idxS2_mem hκ hp
  have b := idxS2_mem hκ hp'
  obtain ⟨w, hs, _, h4⟩ := S2_data (j := j) a.1
  obtain ⟨w', hs', _, h4'⟩ := S2_data (j := j') b.1
  have hme1 : 2 ^ j + 1 + 1 < 2 ^ j' + 1 + 1 → 2 * (2 ^ j + 1) - 2 < 2 * (2 ^ j' + 1) - 2 := by
    intro hl
    have hx : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have hy : 1 ≤ 2 ^ j' := Nat.one_le_two_pow
    omega
  have hme2 : 2 ^ j' + 1 + 1 < 2 ^ j + 1 + 1 → 2 * (2 ^ j' + 1) - 2 < 2 * (2 ^ j + 1) - 2 := by
    intro hl
    have hx : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have hy : 1 ≤ 2 ^ j' := Nat.one_le_two_pow
    omega
  obtain ⟨hm, hh⟩ := symok_inj h4 h4' hs hs' heq hme1 hme2
  have hj : j = j' := by
    have : 2 ^ j = 2 ^ j' := by omega
    exact Nat.pow_right_injective (le_refl 2) this
  subst hj
  have hq : q = q' := by
    have h1 : (2 ^ j + 1 + 1) * q = (2 ^ j + 1 + 1) * q' := by
      unfold hS2 at hh
      omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) h1
  subst hq
  rfl

theorem Sym1_card {H : ℕ} (hH : 3 ≤ H) : (Sym1 H).card = H - 3 := by
  unfold Sym1
  rw [Finset.card_image_of_injOn, Nat.card_Icc]
  · omega
  · intro a ha b hb hab
    have ha' := (Finset.mem_Icc.1 (Finset.mem_coe.1 ha)).1
    have hb' := (Finset.mem_Icc.1 (Finset.mem_coe.1 hb)).1
    have h' : 2 ^ (a - 1) + 1 = 2 ^ (b - 1) + 1 := hab
    have : 2 ^ (a - 1) = 2 ^ (b - 1) := by omega
    have := Nat.pow_right_injective (le_refl 2) this
    omega

theorem Sym12_disj {H κ : ℕ} (hκ : κ ≤ H) : Disjoint (Sym1 H) (Sym2 H κ) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  obtain ⟨_, _, h, _, _, hf1, hx⟩ := Sym1_prop hx1
  obtain ⟨_, _, h', _, _, hf2, hlt⟩ := Sym2_prop hκ hx2
  have : h = h' := by omega
  subst this
  omega

/-- The set of members of Theorem `thm:counting2`. -/
noncomputable def Aset2 (H κ : ℕ) : Finset ℕ := Mset H κ ∪ (Sym1 H ∪ Sym2 H κ)

theorem Aset2_card {H κ : ℕ} (hH : 3 ≤ H) (hκ : κ ≤ H) :
    (Aset2 H κ).card =
      (H + ∑ k ∈ Finset.range (κ + 1), (H - k) / 2 ^ (k + 1)) + (H - 3) +
        ∑ j ∈ Finset.range κ, (H - (j + 1)) / (2 ^ j + 1 + 1) := by
  have hd1 : Disjoint (Mset H κ) (Sym1 H ∪ Sym2 H κ) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have a := (Mset_prop hκ hx1).2
    rcases Finset.mem_union.1 hx2 with hx2 | hx2
    · have b := (Sym1_prop hx2).2.1
      omega
    · have b := (Sym2_prop hκ hx2).2.1
      omega
  unfold Aset2
  rw [card_union_disj hd1, card_union_disj (Sym12_disj hκ), Mset_card hκ, Sym1_card hH,
    Sym2_card hκ, card_idxS2]
  omega

theorem A2_nat {n H κ : ℕ} (hn : 2 ^ (H + 1) ≤ n) (hH : 3 ≤ H) (hκ : κ ≤ H) :
    (H + ∑ k ∈ Finset.range (κ + 1), (H - k) / 2 ^ (k + 1)) + (H - 3) +
        ∑ j ∈ Finset.range κ, (H - (j + 1)) / (2 ^ j + 1 + 1) ≤ Acount n := by
  have hsub : Aset2 H κ ⊆ KA H := by
    intro x hx
    unfold Aset2 at hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact (Mset_prop hκ hx).1
    · rcases Finset.mem_union.1 hx with hx | hx
      · exact (Sym1_prop hx).1
      · exact (Sym2_prop hκ hx).1
  have h1 := Finset.card_le_card hsub
  rw [Aset2_card hH hκ] at h1
  have h2 := KA_le hn
  omega

/-! ### The non-members: `B(n) ≥ H + |N| + |S3|` -/

noncomputable def Sym3 (H κ : ℕ) : Finset ℕ := (idxS3 H κ).image fS3

theorem Sym3_prop {H κ x : ℕ} (hκ : κ ≤ H) (hx : x ∈ Sym3 H κ) :
    x ∈ KB H ∧ 3 * x < 2 * 2 ^ hfun x := by
  obtain ⟨⟨j, q⟩, hp, rfl⟩ := Finset.mem_image.1 hx
  have a := idxS3_mem hκ hp
  obtain ⟨w, hs, hA, h4⟩ := S3_data (j := j) a.1
  obtain ⟨hK2, hf⟩ := symok_hfun h4 hs
  have hpos : 2 ≤ 2 ^ (j + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsep := symok_sep (by omega) h4 hs
  refine ⟨?_, ?_⟩
  · rw [mem_KB]
    refine ⟨hK2, by rw [hf]; exact a.2, ?_⟩
    rw [hf]
    exact hA
  · rw [hf]
    exact hsep

theorem Sym3_card {H κ : ℕ} (hκ : κ ≤ H) : (Sym3 H κ).card = (idxS3 H κ).card := by
  unfold Sym3
  apply Finset.card_image_of_injOn
  rintro ⟨j, q⟩ hp ⟨j', q'⟩ hp' heq
  have a := idxS3_mem hκ hp
  have b := idxS3_mem hκ hp'
  obtain ⟨w, hs, _, h4⟩ := S3_data (j := j) a.1
  obtain ⟨w', hs', _, h4'⟩ := S3_data (j := j') b.1
  obtain ⟨hm, hh⟩ := symok_inj h4 h4' hs hs' heq
    (by
      intro hl
      have : 2 ^ (j + 1) < 2 ^ (j' + 1) := by omega
      omega)
    (by
      intro hl
      have : 2 ^ (j' + 1) < 2 ^ (j + 1) := by omega
      omega)
  have hj : j = j' := by
    have : 2 ^ (j + 1) = 2 ^ (j' + 1) := by omega
    have := Nat.pow_right_injective (le_refl 2) this
    omega
  subst hj
  have hq : q = q' := by
    have h1 : (2 ^ (j + 1) + 1) * q = (2 ^ (j + 1) + 1) * q' := by
      unfold hS3 at hh
      omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) h1
  subst hq
  rfl

/-- The set of non-members of Theorem `thm:counting2`. -/
noncomputable def Bset2 (H κ : ℕ) : Finset ℕ := Nset H κ ∪ Sym3 H κ

theorem Bset2_card {H κ : ℕ} (hH : 3 ≤ H) (hκ : κ ≤ H) :
    (Bset2 H κ).card =
      ((∑ j ∈ Finset.range κ, (H - (j + 1)) / (2 * (2 ^ (j + 1) - 1))) + ((H - 3) / 4 + 1)) +
        ∑ j ∈ Finset.range (κ - 1), (H - (j + 2)) / (2 ^ (j + 1) + 1) := by
  have hd : Disjoint (Nset H κ) (Sym3 H κ) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have a := (Nset_prop hH hκ hx1).2
    have b := (Sym3_prop hκ hx2).2
    omega
  unfold Bset2
  rw [card_union_disj hd, Nset_card hH hκ, Sym3_card hκ, card_idxS3]

theorem B2_nat {n H κ : ℕ} (hn : 2 ^ (H + 1) ≤ n) (hH : 3 ≤ H) (hκ : κ ≤ H) :
    H + ((∑ j ∈ Finset.range κ, (H - (j + 1)) / (2 * (2 ^ (j + 1) - 1))) + ((H - 3) / 4 + 1)) +
        ∑ j ∈ Finset.range (κ - 1), (H - (j + 2)) / (2 ^ (j + 1) + 1) ≤ Bcount n := by
  have hsub : Bset2 H κ ⊆ KB H := by
    intro x hx
    unfold Bset2 at hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact (Nset_prop hH hκ hx).1
    · exact (Sym3_prop hκ hx).1
  have h1 := Finset.card_le_card hsub
  rw [Bset2_card hH hκ] at h1
  have h2 := KB_le hn
  omega

end SequenceNicolas.Counting
