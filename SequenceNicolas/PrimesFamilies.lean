module

public import Mathlib
public import SequenceNicolas.PrimesBase
public import SequenceNicolas.PrimesRep
public import SequenceNicolas.PrimesStep

@[expose] public section

/-!
# The analogue for an arbitrary prime: `thm:primefamilies` and `prop:primezero`

For a candidate `K`, `u = (p-1)K + p` and `g = gexp p K`.
-/

namespace SequenceNicolas.Primes

open scoped Classical

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Theorem `thm:primefamilies` (1) and Proposition `prop:primezero` -/

/-- If `(p-1)K + p = p^g` then `g(K) = g`. -/
theorem gexp_of_pow {K g : ℕ} (hg : 1 ≤ g) (h : (p - 1) * K + p = p ^ g) : gexp p K = g := by
  have hp1 := hp.out.one_lt
  have e : (p - 1) * (K + 1) = (p - 1) * K + (p - 1) := by ring
  apply gexp_eq hg (by omega)
  intro n hn1 hn
  have := pow_lt_pow_p (p := p) hn
  omega

/-- Theorem `thm:primefamilies` (1). -/
theorem primefam_one {K g : ℕ} (hg : 1 ≤ g) (h : (p - 1) * K + p = p ^ g) :
    cp p (p ^ K) = p ^ (K + g - 1) ∧ Ap p (K + g - 1) := by
  have h1 := cp_pow (p := p) K
  have h2 : tt p K = p ^ K * p ^ g := by
    unfold tt
    rw [h]
  have h3 : p ^ (K + g) = p * p ^ (K + g - 1) := by
    obtain ⟨t, ht⟩ : ∃ t, K + g = t + 1 := ⟨K + g - 1, by omega⟩
    rw [ht, Nat.add_sub_cancel]
    ring
  have h4 : p * cp p (p ^ K) = p * p ^ (K + g - 1) := by
    rw [h1, h2, ← pow_add, h3]
  have h5 : cp p (p ^ K) = p ^ (K + g - 1) := Nat.eq_of_mul_eq_mul_left hp.out.pos h4
  exact ⟨h5, ⟨p ^ K, Nat.one_le_pow _ _ hp.out.pos, h5⟩⟩

/-- Every `g ≥ 1` gives the integer `K = (p^g - p)/(p - 1)`. -/
theorem primefam_one_exists {g : ℕ} (hg : 1 ≤ g) : ∃ K, (p - 1) * K + p = p ^ g := by
  obtain ⟨s, hs⟩ : ∃ s, gsum p g = s + 1 := ⟨gsum p g - 1, by have := gsum_pos (p := p) hg; omega⟩
  have h := gsum_spec (p := p) g
  rw [hs, mul_add] at h
  have hp1 := hp.out.one_lt
  exact ⟨s, by omega⟩

/-- Proposition `prop:primezero`: `w₀ = 0` iff `u = p^g`. -/
theorem primezero_iff (K : ℕ) :
    p ^ gexp p K % ((p - 1) * K + p) = 0 ↔ (p - 1) * K + p = p ^ gexp p K := by
  obtain ⟨c1, c2⟩ := cand_data (p := p) K
  have hp1 := hp.out.one_lt
  have e : (p - 1) * (K + 1) = (p - 1) * K + (p - 1) := by ring
  constructor
  · intro h
    have hdvd : ((p - 1) * K + p) ∣ p ^ gexp p K := Nat.dvd_of_mod_eq_zero h
    obtain ⟨c, hc⟩ := hdvd
    have hcd : c ∣ p ^ gexp p K := ⟨(p - 1) * K + p, by rw [hc]; ring⟩
    obtain ⟨k, hk, hck⟩ := (Nat.dvd_prime_pow hp.out).1 hcd
    have hu : 1 ≤ (p - 1) * K + p := by omega
    have hclt : c < p := by
      by_contra hcon
      push Not at hcon
      have : ((p - 1) * K + p) * p ≤ ((p - 1) * K + p) * c := Nat.mul_le_mul_left _ hcon
      have h5 : p * ((p - 1) * (K + 1)) < ((p - 1) * K + p) * p := by
        have h6 : p * (p - 1) < p * p := mlt hp.out.pos (by omega)
        rw [e]
        nlinarith [h6]
      rw [← hc] at this
      omega
    have hk0 : k = 0 := by
      by_contra hk0
      have : p ≤ p ^ k := by
        calc p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ k := Nat.pow_le_pow_right hp.out.pos (by omega)
      rw [← hck] at this
      omega
    rw [hk0, pow_zero] at hck
    rw [hck, mul_one] at hc
    exact hc.symm
  · intro h
    rw [← h]
    exact Nat.mod_self _

/-- Proposition `prop:primezero`: in that case `a ∈ 𝓐_p`. -/
theorem primezero_mem {a K : ℕ} (hK : bp p K = a + 1)
    (h : (p - 1) * K + p = p ^ gexp p K) : Ap p a := by
  rw [primestep_one hK]
  have h0 : p ^ gexp p K % ((p - 1) * K + p) = 0 := (primezero_iff K).2 h
  rw [h0]
  exact ⟨Nat.zero_le _, succ_zero K⟩

/-- Proposition `prop:primezero`, converse: `a` is the exponent of (1) of `thm:primefamilies`. -/
theorem primezero_family {K g : ℕ} (hg : 1 ≤ g) (h : (p - 1) * K + p = p ^ g) :
    bp p K = (K + g - 1) + 1 ∧ p ^ gexp p K % ((p - 1) * K + p) = 0 := by
  have hg' := gexp_of_pow (p := p) hg h
  refine ⟨?_, ?_⟩
  · unfold bp
    rw [hg']
    omega
  · rw [primezero_iff, hg']
    exact h

/-! ### Theorem `thm:primefamilies` (2) -/

theorem cp_pow_pred_mul (m : ℕ) : p * cp p (p ^ m - 1) = p ^ m * ((p - 1) * m) := by
  have h1 := cp_pow_pred (p := p) m
  have h2 : tt p m = p ^ m * ((p - 1) * m) + p ^ m * p := by
    unfold tt
    rw [mul_add]
  have h3 : p * p ^ m = p ^ m * p := mul_comm _ _
  omega

/-- Theorem `thm:primefamilies` (2). -/
theorem primefam_two (hp2 : p ≠ 2) {m : ℕ} : ¬ ∃ a, cp p (p ^ m - 1) = p ^ a := by
  rintro ⟨a, ha⟩
  have h := cp_pow_pred_mul (p := p) m
  rw [ha, ← pow_succ'] at h
  have h1 : p - 1 ∣ p ^ (a + 1) := ⟨p ^ m * m, by rw [h]; ring⟩
  have h2 : p - 1 ∣ p ^ (a + 1) - 1 := by
    exact sub_one_dvd_pow_sub_one p (a + 1) hp.out.one_lt.le
  have h3 : p - 1 ∣ p ^ (a + 1) - (p ^ (a + 1) - 1) := by
    exact Nat.dvd_sub h1 h2
  have h4 : p ^ (a + 1) - (p ^ (a + 1) - 1) = 1 := by
    have := pow_pos hp.out.pos (a + 1)
    omega
  rw [h4] at h3
  have h5 := Nat.dvd_one.1 h3
  have := hp.out.two_le
  omega

/-! ### Theorem `thm:primefamilies` (3) -/

/-- For `p` odd and `g ≥ 2` even, `K = (p^g - 2p + 1)/(2(p-1))` is an integer. -/
theorem primefam_three_exists (hp2 : p ≠ 2) {g : ℕ} (hg : 2 ≤ g) (hev : Even g) :
    ∃ K, 2 * ((p - 1) * K + p) = p ^ g + 1 := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  obtain ⟨q, hq⟩ : ∃ q, p = 2 * q + 1 := by
    rcases hp.out.eq_two_or_odd' with h | ⟨q, hq⟩
    · exact absurd h hp2
    · exact ⟨q, hq⟩
  obtain ⟨h, hh⟩ := hev
  have hP : p ^ g = (p ^ 2) ^ h := by
    rw [hh, ← two_mul, pow_mul]
  have hd : p ^ 2 - 1 ∣ (p ^ 2) ^ h - 1 := by
    exact sub_one_dvd_pow_sub_one (p ^ 2) h (Nat.one_le_pow 2 p hp.out.pos)
  have hp2' : p ^ 2 - 1 = 4 * q * (q + 1) := by
    have : p ^ 2 = 4 * q * (q + 1) + 1 := by rw [hq]; ring
    omega
  rw [hp2', ← hP] at hd
  obtain ⟨N, hN⟩ := hd
  have hPpos : 3 ≤ p ^ g := by
    calc 3 ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ g := Nat.pow_le_pow_right hp.out.pos (by omega)
  have hP1 : p ^ g = 4 * q * (q + 1) * N + 1 := by omega
  obtain ⟨M', hM'⟩ : ∃ M', (q + 1) * N = M' + 1 := by
    refine ⟨(q + 1) * N - 1, ?_⟩
    have : 0 < (q + 1) * N := by
      apply Nat.pos_of_ne_zero
      intro h0
      have : 4 * q * (q + 1) * N = 4 * q * ((q + 1) * N) := by ring
      rw [h0] at this
      omega
    omega
  have key : 4 * q * (q + 1) * N = 4 * q * (M' + 1) := by
    rw [show 4 * q * (q + 1) * N = 4 * q * ((q + 1) * N) by ring, hM']
  have hp1 : p - 1 = 2 * q := by omega
  refine ⟨M', ?_⟩
  rw [hp1, hP1, key, hq]
  ring

/-- Theorem `thm:primefamilies` (3): the candidate exponent is `K + g - 1`, which is not in `𝓐_p`. -/
theorem primefam_three {K g : ℕ} (hp2 : p ≠ 2) (hg : 1 ≤ g)
    (h : 2 * ((p - 1) * K + p) = p ^ g + 1) :
    gexp p K = g ∧ bp p K = (K + g - 1) + 1 ∧ ¬ Ap p (K + g - 1) ∧
      p ^ g % ((p - 1) * K + p) = (p - 1) * K + p - 1 := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have e : (p - 1) * (K + 1) = (p - 1) * K + (p - 1) := by ring
  have hgx : gexp p K = g := by
    apply gexp_eq hg (by omega)
    intro n hn1 hn
    obtain ⟨g', hg'⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    have h1 : p ^ n ≤ p ^ g' := pow_le_pow_p (by omega)
    have h2 : p ^ (g' + 1) = p ^ g' * p := pow_succ _ _
    have h3 : p ^ g' * 3 ≤ p ^ g' * p := Nat.mul_le_mul_left _ hp3
    rw [hg'] at h
    omega
  have hbp : bp p K = (K + g - 1) + 1 := by
    unfold bp
    rw [hgx]
    omega
  have hmod : p ^ g % ((p - 1) * K + p) = (p - 1) * K + p - 1 := by
    have hd : p ^ g = ((p - 1) * K + p) + ((p - 1) * K + p - 1) := by omega
    rw [hd, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hgx, hbp, ?_, hmod⟩
  intro hA
  have := (primestep_one (p := p) hbp).1 hA
  rw [hgx, hmod] at this
  have h5 := this.1
  omega

end SequenceNicolas.Primes
