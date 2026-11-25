module

public import Mathlib
public import SequenceNicolas.Core
public import SequenceNicolas.Recursion
public import SequenceNicolas.States
public import SequenceNicolas.Forest

@[expose] public section

/-!
# The families obtained from the symmetry (Theorem `thm:symfamilies`)

Part (1) is `symfam_one`, part (2) is `symfam_two` and part (3) is `symfam_three`.
The statements avoid division: `w (2^m - 1) + 2^i = 2^h` replaces `w = (2^h - 2σ + 2)/(2^m - 1)`,
`2K = 2^h + w + 2` replaces `K = 2^{h-1} + 1 + w/2`, and `2^i = 2σ - 2` for `σ = 2^{i-1} + 1`.
-/

namespace SequenceNicolas.SymFamilies

open SequenceNicolas.Recursion SequenceNicolas.States SequenceNicolas.Forest

/-! ### Part (1): `c(2^{2^r} - 1) = 2^{2^r + r - 1}` -/

theorem c_pred_pow {k : ℕ} (_hk : 1 ≤ k) :
    2 * SequenceNicolas.Core.c (2 ^ k - 1) = 2 ^ k * k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpos : 0 < 2 ^ k := by positivity
  obtain ⟨n, hn⟩ : ∃ n, 2 ^ k = n + 1 := ⟨2 ^ k - 1, by omega⟩
  have h1 := SequenceNicolas.Core.c_succ n
  rw [← hn, padicValNat.prime_pow] at h1
  have h2 := SequenceNicolas.Core.two_mul_c_pow k
  have e : 2 ^ k * (k + 2) = 2 ^ k * k + 2 * 2 ^ k := by ring
  have e2 : 2 ^ k - 1 = n := by omega
  rw [e2]
  omega

/-- Theorem `thm:symfamilies` (1): `c(2^{2^r} - 1) = 2^{2^r + r - 1}`, and the candidate of the
exponent `2^r + r - 1` is `K = 2^r + 1`. -/
theorem symfam_one (r : ℕ) :
    2 * SequenceNicolas.Core.c (2 ^ (2 ^ r) - 1) = 2 ^ (2 ^ r + r) ∧
    Amem (2 ^ r + r - 1) ∧ beta (2 ^ r + 1) = (2 ^ r + r - 1) + 3 := by
  have hk : 1 ≤ 2 ^ r := by
    have : 0 < 2 ^ r := by positivity
    omega
  have h := c_pred_pow hk
  have e : 2 ^ (2 ^ r) * 2 ^ r = 2 ^ (2 ^ r + r) := by rw [pow_add]
  refine ⟨by rw [h, e], ?_, ?_⟩
  · unfold Amem
    refine ⟨2 ^ (2 ^ r) - 1, ?_⟩
    have e2 : 2 ^ (2 ^ r + r) = 2 * 2 ^ (2 ^ r + r - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  · have := beta_two_pow_succ (r := r)
    omega

/-! ### Residues modulo `2^m - 1` -/

theorem pow_mod_mersenne (m e : ℕ) : 2 ^ e ≡ 2 ^ (e % m) [MOD 2 ^ m - 1] := by
  have h1 : 1 ≤ 2 ^ m := by
    have : 0 < 2 ^ m := by positivity
    omega
  have hm1 : 1 ≡ 2 ^ m [MOD 2 ^ m - 1] := (Nat.modEq_iff_dvd' h1).2 (dvd_refl _)
  have hq := (hm1.symm).pow (e / m)
  rw [one_pow, ← pow_mul] at hq
  have hq2 := hq.mul_right (2 ^ (e % m))
  rw [one_mul, ← pow_add] at hq2
  have he : m * (e / m) + e % m = e := Nat.div_add_mod e m
  rw [he] at hq2
  exact hq2

theorem exists_w {m h i : ℕ} (hh : h % m = i % m) (hle : 2 ^ i ≤ 2 ^ h) :
    ∃ w, w * (2 ^ m - 1) + 2 ^ i = 2 ^ h := by
  have hmod : 2 ^ h ≡ 2 ^ i [MOD 2 ^ m - 1] := by
    have a := pow_mod_mersenne m h
    have b := pow_mod_mersenne m i
    rw [hh] at a
    exact a.trans b.symm
  have hd := (Nat.modEq_iff_dvd' hle).1 hmod.symm
  obtain ⟨w, hw⟩ := hd
  refine ⟨w, ?_⟩
  have hc : w * (2 ^ m - 1) = (2 ^ m - 1) * w := Nat.mul_comm _ _
  omega

/-! ### Reduction to the state `(J, w)` -/

/-- With `2J = 2^h + w`, `w + 1 ≤ J` and `J + 1 ≤ 2^h`, the exponent `J + h - 2` has candidate
`J + 1` and belongs to `𝓐` iff the state `(J, w)` is successful. -/
theorem amem_iff_succ {J w h : ℕ} (hJ : 1 ≤ J) (hw : w + 1 ≤ J) (hsum : 2 * J = 2 ^ h + w)
    (hb : J + 1 ≤ 2 ^ h) : Amem (J + h - 2) ↔ Succ J w := by
  have hb2 : 2 ^ h < 2 * (J + 1) := by omega
  have hH : hfun (J + 1) = h := hfun_of_bounds (by omega : 2 ≤ J + 1) hb hb2
  have hh1 : 1 ≤ h := by
    by_contra hc
    have h0 : h = 0 := by omega
    rw [h0] at hb
    norm_num at hb
    omega
  have hbeta : beta (J + 1) = (J + h - 2) + 3 := by
    unfold beta
    rw [hH]
    omega
  rw [amem_iff_state hJ hbeta, hH]
  have e : 2 ^ h - (J + 1) = J - 1 - w := by omega
  rw [e]
  exact (succ_symm hJ hw).symm

theorem fam_bounds {w J h : ℕ} (hh : 4 ≤ h) (hw1 : 1 ≤ w) (hw7 : w * 7 ≤ 2 ^ h)
    (h2J : 2 * J = 2 ^ h + w) :
    2 ∣ w ∧ 2 ^ (h - 1) + 1 < J + 1 ∧ J + 1 < 2 ^ h ∧ 2 ≤ J ∧ w + 1 ≤ J ∧ J + 1 ≤ 2 ^ h := by
  have e : 2 ^ h = 2 * 2 ^ (h - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h8 : 2 ^ 3 ≤ 2 ^ (h - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h8' : (2 : ℕ) ^ 3 = 8 := by norm_num
  have hev : 2 ∣ 2 ^ h := dvd_pow_self 2 (by omega)
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-! ### Part (2): the members -/

/-- Theorem `thm:symfamilies` (2): `σ = 2^{i-1} + 1`, `h ≥ σ + 2`, `h ≡ i (mod σ + 1)`. -/
theorem symfam_two {i σ h : ℕ} (hi : 1 ≤ i) (hσ : σ = 2 ^ (i - 1) + 1) (hh : σ + 2 ≤ h)
    (hmod : h % (σ + 1) = i % (σ + 1)) :
    ∃ w K, w * (2 ^ (σ + 1) - 1) + (2 * σ - 2) = 2 ^ h ∧ 2 ∣ w ∧ 1 ≤ w ∧
      2 * K = 2 ^ h + w + 2 ∧ 2 ^ (h - 1) + 1 < K ∧ K < 2 ^ h ∧ Amem (K + h - 3) := by
  have hi1 : 2 ^ i = 2 * 2 ^ (i - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpos : 0 < 2 ^ (i - 1) := by positivity
  have hσ2 : 2 ≤ σ := by omega
  have hiσ : i ≤ σ := by
    have := nat_lt_two_pow (i - 1)
    omega
  have hpi : 2 ^ i = 2 * σ - 2 := by omega
  have hlt : 2 ^ i < 2 ^ h := by
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨w, hw⟩ := exists_w (m := σ + 1) hmod hlt.le
  obtain ⟨P, hP⟩ : ∃ P, 2 ^ (σ + 1) = P + 1 :=
    ⟨2 ^ (σ + 1) - 1, by
      have : 0 < 2 ^ (σ + 1) := by positivity
      omega⟩
  have hPm : 2 ^ (σ + 1) - 1 = P := by omega
  rw [hPm] at hw
  have hw1 : 1 ≤ w := by
    by_contra hc
    have : w = 0 := by omega
    rw [this] at hw
    omega
  have h8 : 2 ^ 3 ≤ 2 ^ (σ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e8 : (2 : ℕ) ^ 3 = 8 := by norm_num
  have hP7 : 7 ≤ P := by omega
  have hw7 : w * 7 ≤ 2 ^ h := by
    have := Nat.mul_le_mul_left w hP7
    omega
  have h4 : 2 ^ 2 ≤ 2 ^ σ := Nat.pow_le_pow_right (by norm_num) hσ2
  have e4 : (2 : ℕ) ^ 2 = 4 := by norm_num
  have hge : 2 ^ σ * 1 ≤ 2 ^ σ * w := Nat.mul_le_mul_left _ hw1
  obtain ⟨J', hJ'⟩ : ∃ J', J' + 1 = 2 ^ σ * w := ⟨2 ^ σ * w - 1, by omega⟩
  have hpw : w * 2 ^ (σ + 1) = 2 * (2 ^ σ * w) := by ring
  have hwP : w * 2 ^ (σ + 1) = w * P + w := by rw [hP]; ring
  have h2J : 2 * (J' + σ) = 2 ^ h + w := by omega
  obtain ⟨hev, hK1, hK2, hJ2, hwJ, hbJ⟩ := fam_bounds (by omega : 4 ≤ h) hw1 hw7 h2J
  have hstJ : IsState (J' + σ) w := ⟨by omega, hwJ⟩
  have hstJ' : IsState J' 0 := ⟨by omega, by omega⟩
  have hphi : Phi (J' + σ) w J' 0 := by
    rw [children_eq hstJ']
    have e : σ - 1 + 1 = σ := by omega
    refine ⟨σ - 1, ?_, ?_, ?_⟩
    · rw [e]
      exact ⟨w, by omega⟩
    · rw [e]
    · rw [e]
      have hp : 0 < 2 ^ σ := by positivity
      have : J' + 1 + 0 = 2 ^ σ * w := by omega
      rw [this, Nat.mul_div_cancel_left w hp]
  have hsucc : Succ (J' + σ) w :=
    (succ_iff_phi hstJ).2 (Or.inr ⟨J', 0, hphi, succ_zero J'⟩)
  have hA := (amem_iff_succ (by omega : 1 ≤ J' + σ) hwJ h2J hbJ).2 hsucc
  refine ⟨w, J' + σ + 1, ?_, hev, hw1, by omega, hK1, hK2, ?_⟩
  · rw [hPm]
    omega
  · have e : J' + σ + 1 + h - 3 = J' + σ + h - 2 := by omega
    rw [e]
    exact hA

/-! ### Part (3): the non-members -/

/-- Theorem `thm:symfamilies` (3): `i ≥ 2`, `σ = 2^{i-1} + 1`, `h ≥ σ + 1`, `h ≡ i (mod σ)`. -/
theorem symfam_three {i σ h : ℕ} (hi : 2 ≤ i) (hσ : σ = 2 ^ (i - 1) + 1) (hh : σ + 1 ≤ h)
    (hmod : h % σ = i % σ) :
    ∃ w K, w * (2 ^ σ - 1) + (2 * σ - 2) = 2 ^ h ∧ 2 ∣ w ∧ 1 ≤ w ∧
      2 * K = 2 ^ h + w + 2 ∧ 2 ^ (h - 1) + 1 < K ∧ K < 2 ^ h ∧ ¬ Amem (K + h - 3) := by
  have hi1 : 2 ^ i = 2 * 2 ^ (i - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpos : 0 < 2 ^ (i - 1) := by positivity
  have h2 : 2 ^ 1 ≤ 2 ^ (i - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e2 : (2 : ℕ) ^ 1 = 2 := by norm_num
  have hσ3 : 3 ≤ σ := by omega
  have hiσ : i ≤ σ := by
    have := nat_lt_two_pow (i - 1)
    omega
  have hpi : 2 ^ i = 2 * σ - 2 := by omega
  have hlt : 2 ^ i < 2 ^ h := by
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨w, hw⟩ := exists_w (m := σ) hmod hlt.le
  obtain ⟨P, hP⟩ : ∃ P, 2 ^ σ = P + 1 :=
    ⟨2 ^ σ - 1, by
      have : 0 < 2 ^ σ := by positivity
      omega⟩
  have hPm : 2 ^ σ - 1 = P := by omega
  rw [hPm] at hw
  have hw1 : 1 ≤ w := by
    by_contra hc
    have : w = 0 := by omega
    rw [this] at hw
    omega
  have h8 : 2 ^ 3 ≤ 2 ^ σ := Nat.pow_le_pow_right (by norm_num) hσ3
  have e8 : (2 : ℕ) ^ 3 = 8 := by norm_num
  have hP7 : 7 ≤ P := by omega
  have hw7 : w * 7 ≤ 2 ^ h := by
    have := Nat.mul_le_mul_left w hP7
    omega
  obtain ⟨t, ht⟩ : ∃ t, σ = t + 1 := ⟨σ - 1, by omega⟩
  have hpt : 2 ^ σ = 2 * 2 ^ t := by
    rw [ht]
    ring
  have hpw : w * 2 ^ σ = 2 * (2 ^ t * w) := by
    rw [hpt]
    ring
  have hwP : w * 2 ^ σ = w * P + w := by rw [hP]; ring
  obtain ⟨J, hJ⟩ : ∃ J, J = 2 ^ t * w + t := ⟨_, rfl⟩
  have h2J : 2 * J = 2 ^ h + w := by omega
  obtain ⟨hev, hK1, hK2, hJ2, hwJ, hbJ⟩ := fam_bounds (by omega : 4 ≤ h) hw1 hw7 h2J
  have hstJ : IsState J w := ⟨by omega, hwJ⟩
  have hfail : Fails J w :=
    (fails_iff hstJ hw1).2 ⟨t, by omega, by omega⟩
  have hA := amem_iff_succ (by omega : 1 ≤ J) hwJ h2J hbJ
  refine ⟨w, J + 1, ?_, hev, hw1, by omega, hK1, hK2, ?_⟩
  · rw [hPm]
    omega
  · have e : J + 1 + h - 3 = J + h - 2 := by omega
    rw [e]
    intro hmem
    exact not_succ_of_fails hstJ hw1 hfail (hA.1 hmem)

end SequenceNicolas.SymFamilies
