module

public import Mathlib
public import SequenceNicolas.PrimesBase

@[expose] public section

/-!
# The analogue for an arbitrary prime: Theorem `thm:primes`

`InEp p K V` says `V ∈ 𝓔^{(p)}_K`, `Ap p a` says `a ∈ 𝓐_p`, `gexp p K` is the integer `g(K)` and
`gap g = (p^g - 1)/(p - 1)` is written as the sum `∑_{i<g} p^i`.
-/

namespace SequenceNicolas.Primes

open scoped Classical

/-- `V ∈ 𝓔^{(p)}_K`: `V = ∑_{i<K} d_i t_i` with `0 ≤ d_i ≤ p - 1`. -/
def InEp (p K V : ℕ) : Prop := ∃ d : ℕ → ℕ, (∀ i, d i ≤ p - 1) ∧ V = esum p d K

/-- `a ∈ 𝓐_p`: `p^a` is a value of `c_p`. -/
def Ap (p a : ℕ) : Prop := ∃ n, 1 ≤ n ∧ cp p n = p ^ a

/-- `(p^g - 1)/(p - 1) = ∑_{i<g} p^i`. -/
def gsum (p g : ℕ) : ℕ := ∑ i ∈ Finset.range g, p ^ i

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
theorem lt_pow' (hp2 : 2 ≤ p) (n : ℕ) : n < p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : p ^ (n + 1) = p * p ^ n := by ring
    have h2 : 2 * p ^ n ≤ p * p ^ n := Nat.mul_le_mul_right _ hp2
    omega

theorem tt_pos (K : ℕ) : 0 < tt p K := by
  unfold tt
  have h1 : 0 < p ^ K := pow_pos hp.out.pos K
  have h2 := hp.out.pos
  exact Nat.mul_pos h1 (by omega)

omit hp in
theorem tt_succ_eq (K : ℕ) : tt p K = p ^ K * ((p - 1) * K + p) := rfl

omit hp in
theorem esum_succ (d : ℕ → ℕ) (K : ℕ) : esum p d (K + 1) = esum p d K + d K * tt p K := by
  unfold esum
  rw [Finset.sum_range_succ]

/-! ### Theorem `thm:primes` (1) -/

omit hp in
theorem dval_mod (n K : ℕ) : dval p (fun i => n / p ^ i % p) K = n % p ^ K := by
  induction K with
  | zero =>
    simp [dval]
    omega
  | succ K ih =>
    have h1 : dval p (fun i => n / p ^ i % p) (K + 1)
        = dval p (fun i => n / p ^ i % p) K + (n / p ^ K % p) * p ^ K := by
      unfold dval
      rw [Finset.sum_range_succ]
    have h2 : n % p ^ (K + 1) = n % p ^ K + p ^ K * (n / p ^ K % p) := by
      exact Nat.mod_pow_succ
    rw [h1, ih, h2]
    ring

theorem Ap_iff (a : ℕ) :
    Ap p a ↔ ∃ K d, (∀ i, d i ≤ p - 1) ∧ (∃ i, i < K ∧ d i ≠ 0) ∧ p ^ (a + 1) = esum p d K := by
  constructor
  · rintro ⟨n, hn, hc⟩
    have hd : ∀ i, (fun i => n / p ^ i % p) i ≤ p - 1 := by
      intro i
      have := Nat.mod_lt (n / p ^ i) hp.out.pos
      show n / p ^ i % p ≤ p - 1
      omega
    have hlt : n < p ^ n := lt_pow' hp.out.two_le n
    have hv : dval p (fun i => n / p ^ i % p) n = n := by
      rw [dval_mod, Nat.mod_eq_of_lt hlt]
    refine ⟨n, fun i => n / p ^ i % p, hd, ?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      have : dval p (fun i => n / p ^ i % p) n = 0 := by
        unfold dval
        apply Finset.sum_eq_zero
        intro i hi
        simp [hcon i (Finset.mem_range.1 hi)]
      omega
    · have := cp_digits (K := n) hd
      rw [hv, hc] at this
      rw [← this]
      ring
  · rintro ⟨K, d, hd, ⟨i, hi, hdi⟩, he⟩
    have hn : 1 ≤ dval p d K := by
      have h1 : d i * p ^ i ≤ dval p d K := by
        unfold dval
        exact Finset.single_le_sum (f := fun i => d i * p ^ i) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hi)
      have h2 : 0 < d i := Nat.pos_of_ne_zero hdi
      have h3 : 0 < p ^ i := pow_pos hp.out.pos i
      have := Nat.mul_pos h2 h3
      omega
    refine ⟨dval p d K, hn, ?_⟩
    have h := cp_digits hd K
    rw [← he, pow_succ'] at h
    exact Nat.eq_of_mul_eq_mul_left hp.out.pos (by rw [h])

/-! ### Theorem `thm:primes` (2) -/

theorem sum_pm1 (m : ℕ) : ∑ i ∈ Finset.range m, (p - 1) * tt p i = m * (p - 1) * p ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.one_lt; omega⟩
    have hq1 : p - 1 = q := by omega
    unfold tt
    rw [hq1, hq]
    ring

theorem sum_pm1_lt (m : ℕ) : m * (p - 1) * p ^ m < tt p m := by
  unfold tt
  have hP : 0 < p ^ m := pow_pos hp.out.pos m
  have := Nat.mul_pos hP hp.out.pos
  nlinarith [this]

theorem esum_le {d : ℕ → ℕ} (hd : ∀ i, d i ≤ p - 1) (K : ℕ) :
    esum p d K ≤ K * (p - 1) * p ^ K := by
  rw [← sum_pm1]
  unfold esum
  apply Finset.sum_le_sum
  intro i _
  exact Nat.mul_le_mul_right _ (hd i)

theorem esum_lt {d : ℕ → ℕ} (hd : ∀ i, d i ≤ p - 1) (K : ℕ) : esum p d K < tt p K :=
  lt_of_le_of_lt (esum_le hd K) (sum_pm1_lt K)

/-- The top digit is `⌊V/t_K⌋`. -/
theorem top_digit {d : ℕ → ℕ} (hd : ∀ i, d i ≤ p - 1) (K : ℕ) :
    d K = esum p d (K + 1) / tt p K ∧ esum p d (K + 1) % tt p K = esum p d K := by
  have hpos := tt_pos (p := p) K
  have hlt := esum_lt hd K
  rw [esum_succ]
  have e : esum p d K + d K * tt p K = esum p d K + tt p K * d K := by rw [mul_comm (d K)]
  rw [e, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlt, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hlt]
  exact ⟨by simp, rfl⟩

/-- The representation of `V` with digits in `[0, p-1]` is unique. -/
theorem rep_unique {d d' : ℕ → ℕ} (hd : ∀ i, d i ≤ p - 1) (hd' : ∀ i, d' i ≤ p - 1) (K : ℕ)
    (h : esum p d K = esum p d' K) : ∀ i, i < K → d i = d' i := by
  induction K with
  | zero => intro i hi; omega
  | succ K ih =>
    obtain ⟨a1, a2⟩ := top_digit hd K
    obtain ⟨b1, b2⟩ := top_digit hd' K
    have hK : d K = d' K := by rw [a1, b1, h]
    have hE : esum p d K = esum p d' K := by
      rw [← a2, ← b2, h]
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · exact ih hE i hi
    · rw [hi]; exact hK

/-! ### Theorem `thm:primes` (3) -/

theorem exists_g (p K : ℕ) (hp2 : 2 ≤ p) : ∃ g, 1 ≤ g ∧ (p - 1) * (K + 1) + 1 ≤ p ^ g := by
  refine ⟨(p - 1) * (K + 1) + 1, by omega, ?_⟩
  exact (lt_pow' hp2 _).le

/-- `g(K)`: the least `g ≥ 1` with `p^g ≥ (p - 1)(K + 1) + 1`. -/
noncomputable def gexp (p K : ℕ) : ℕ :=
  if h : 2 ≤ p then Nat.find (exists_g p K h) else 0

theorem gexp_spec (K : ℕ) : 1 ≤ gexp p K ∧ (p - 1) * (K + 1) + 1 ≤ p ^ gexp p K := by
  unfold gexp
  split_ifs with h2
  · exact Nat.find_spec (exists_g p K h2)
  · exact absurd hp.out.two_le h2

theorem gexp_min {K g : ℕ} (hg1 : 1 ≤ g) (hg : (p - 1) * (K + 1) + 1 ≤ p ^ g) : gexp p K ≤ g := by
  unfold gexp
  split_ifs with h2
  · exact Nat.find_min' _ ⟨hg1, hg⟩
  · exact absurd hp.out.two_le h2

theorem gexp_eq {K g : ℕ} (hg1 : 1 ≤ g) (hg : (p - 1) * (K + 1) + 1 ≤ p ^ g)
    (hmin : ∀ n, 1 ≤ n → n < g → p ^ n < (p - 1) * (K + 1) + 1) : gexp p K = g := by
  apply le_antisymm (gexp_min hg1 hg)
  by_contra hc
  push Not at hc
  obtain ⟨s1, s2⟩ := gexp_spec (p := p) K
  have := hmin _ s1 hc
  omega

/-- The candidate map `K ↦ K + g(K)`. -/
noncomputable def bp (p K : ℕ) : ℕ := K + gexp p K

theorem pow_le_pow_p {a b : ℕ} (h : a ≤ b) : p ^ a ≤ p ^ b :=
  Nat.pow_le_pow_right hp.out.pos h

theorem pow_lt_pow_p {a b : ℕ} (h : a < b) : p ^ a < p ^ b :=
  Nat.pow_lt_pow_right hp.out.one_lt h

theorem lt_of_pow_lt {a b : ℕ} (h : p ^ a < p ^ b) : a < b := by
  by_contra hc
  push Not at hc
  have := pow_le_pow_p (p := p) hc
  omega

/-- Theorem `thm:primes` (3), first part: the largest index and the top digit. -/
theorem top_index {d : ℕ → ℕ} (hd : ∀ i, d i ≤ p - 1) {K b : ℕ} (hK : d K ≠ 0)
    (hV : p ^ b = esum p d (K + 1)) :
    b = K + gexp p K ∧ d K = p ^ gexp p K / ((p - 1) * K + p) ∧ 1 ≤ d K ∧ d K ≤ p - 1 := by
  have hp2 := hp.out.two_le
  have hdK := hd K
  have hpos := tt_pos (p := p) K
  have h1 : tt p K ≤ p ^ b := by
    rw [hV, esum_succ]
    have : tt p K ≤ d K * tt p K := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hK)
    omega
  have h2 : p ^ b ≤ (K + 1) * (p - 1) * p ^ (K + 1) := by
    rw [hV]
    exact esum_le hd (K + 1)
  set u' := (p - 1) * K + p with hu'
  have hu2 : p ≤ u' := by omega
  have htt : tt p K = p ^ K * u' := rfl
  have hPK : 0 < p ^ K := pow_pos hp.out.pos K
  have hKb : K < b := by
    by_contra hc
    push Not at hc
    have := pow_le_pow_p (p := p) hc
    have h3 : p ^ K * 2 ≤ p ^ K * u' := Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨γ, rfl⟩ : ∃ γ, b = K + γ := ⟨b - K, by omega⟩
  have hγ1 : 1 ≤ γ := by omega
  have e1 : p ^ (K + γ) = p ^ K * p ^ γ := pow_add _ _ _
  have e2 : (K + 1) * (p - 1) * p ^ (K + 1) = p ^ K * ((K + 1) * (p - 1) * p) := by ring
  rw [e1, htt] at h1
  rw [e1, e2] at h2
  have hlow : u' ≤ p ^ γ := Nat.le_of_mul_le_mul_left h1 hPK
  have hup : p ^ γ ≤ (K + 1) * (p - 1) * p := Nat.le_of_mul_le_mul_left h2 hPK
  have he : (p - 1) * (K + 1) + 1 = u' := by
    rw [hu']
    have := hp.out.one_lt
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have hq1 : p - 1 = q := by omega
    rw [hq1, hq]
    ring
  have hg : gexp p K = γ := by
    apply gexp_eq hγ1 (by rw [he]; exact hlow)
    intro n hn1 hnγ
    by_contra hc
    push Not at hc
    rw [he] at hc
    have h5 : p ^ (n + 1) ≤ p ^ γ := pow_le_pow_p (by omega)
    have h6 : p ^ (n + 1) = p * p ^ n := by ring
    have h7 : p * u' ≤ p * p ^ n := Nat.mul_le_mul_left p hc
    have h8 : p * u' = (K + 1) * (p - 1) * p + p := by
      rw [hu']
      obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      have hq1 : p - 1 = q := by omega
      rw [hq1, hq]
      ring
    omega
  refine ⟨by rw [hg], ?_, Nat.pos_of_ne_zero hK, hdK⟩
  obtain ⟨t1, _⟩ := top_digit hd K
  rw [t1, ← hV, e1, htt, hg]
  exact Nat.mul_div_mul_left _ _ hPK

/-- `(p - 1) ∑_{i<g} p^i + 1 = p^g`. -/
theorem gsum_spec (g : ℕ) : (p - 1) * gsum p g + 1 = p ^ g := by
  induction g with
  | zero => simp [gsum]
  | succ g ih =>
    have h1 : gsum p (g + 1) = gsum p g + p ^ g := by
      unfold gsum
      rw [Finset.sum_range_succ]
    have h2 := pm1 hp.out.one_lt.le (p ^ g)
    have h3 : p ^ (g + 1) = p * p ^ g := by ring
    rw [h1, mul_add]
    omega

theorem gsum_pos {g : ℕ} (hg : 1 ≤ g) : 1 ≤ gsum p g := by
  unfold gsum
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  rw [Finset.sum_range_succ]
  have := pow_pos hp.out.pos g'
  omega

theorem gexp_mono (K : ℕ) : gexp p K ≤ gexp p (K + 1) := by
  obtain ⟨s1, s2⟩ := gexp_spec (p := p) (K + 1)
  apply gexp_min s1
  have : (p - 1) * (K + 1) ≤ (p - 1) * (K + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem gexp_step (K : ℕ) : gexp p (K + 1) ≤ gexp p K + 1 := by
  obtain ⟨s1, s2⟩ := gexp_spec (p := p) K
  apply gexp_min (by omega)
  have h1 : p ^ (gexp p K + 1) = p * p ^ gexp p K := by ring
  have h2 : p * ((p - 1) * (K + 1) + 1) ≤ p * p ^ gexp p K := Nat.mul_le_mul_left p s2
  have h3 : (p - 1) * (K + 1 + 1) + 1 ≤ p * ((p - 1) * (K + 1) + 1) := by
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.one_lt; omega⟩
    have hq1 : p - 1 = q := by omega
    rw [hq1, hq]
    nlinarith [Nat.zero_le (q * (K + 1)), Nat.zero_le (q * q * (K + 1))]
  omega

theorem bp_strictMono : StrictMono (bp p) := by
  apply strictMono_nat_of_lt_succ
  intro K
  unfold bp
  have := gexp_mono (p := p) K
  omega

theorem bp_zero : bp p 0 = 1 := by
  unfold bp
  have : gexp p 0 = 1 := by
    apply gexp_eq (by norm_num) (by rw [pow_one]; have := hp.out.one_lt; omega)
    intro n hn1 hn
    omega
  simp [this]

/-- The values missed by `K ↦ K + g(K)`: `b ≥ 1` is not of the form `K + g(K)` if and only if
`b = (p^g - 1)/(p - 1) + g` for some `g ≥ 1` (Theorem `thm:primes` (3)). -/
theorem bp_gap_of {g : ℕ} (hg : 1 ≤ g) : ¬ ∃ K, bp p K = gsum p g + g := by
  rintro ⟨K, hK⟩
  have hR := gsum_pos (p := p) hg
  have hs := gsum_spec (p := p) g
  have hp1 := hp.out.one_lt
  have hP : p ^ g ≥ 1 := Nat.one_le_pow _ _ hp.out.pos
  -- K0 = gsum - 1
  have hg0 : gexp p (gsum p g - 1) = g := by
    apply gexp_eq hg
    · have : (gsum p g - 1) + 1 = gsum p g := by omega
      rw [this]
      omega
    · intro n hn1 hn
      have := pow_lt_pow_p (p := p) hn
      have : (gsum p g - 1) + 1 = gsum p g := by omega
      rw [this]
      omega
  have hg1 : gexp p (gsum p g - 1 + 1) = g + 1 := by
    have e : gsum p g - 1 + 1 = gsum p g := by omega
    rw [e]
    apply gexp_eq (by omega)
    · have h1 : p ^ (g + 1) = p * p ^ g := by ring
      have h2 := pm1 hp1.le (p ^ g)
      have h3 : (p - 1) * (gsum p g + 1) = (p - 1) * gsum p g + (p - 1) := by ring
      have h4 : p - 1 ≤ (p - 1) * p ^ g := Nat.le_mul_of_pos_right _ (by omega)
      omega
    · intro n hn1 hn
      have h1 : p ^ n ≤ p ^ g := pow_le_pow_p (by omega)
      have h3 : (p - 1) * (gsum p g + 1) = (p - 1) * gsum p g + (p - 1) := by ring
      omega
  have hm := bp_strictMono (p := p)
  have hlow : bp p (gsum p g - 1) = gsum p g + g - 1 := by
    unfold bp
    rw [hg0]
    omega
  have hhigh : bp p (gsum p g - 1 + 1) = gsum p g + g + 1 := by
    unfold bp
    rw [hg1]
    omega
  rcases lt_trichotomy K (gsum p g - 1) with hl | he | hgt
  · have := hm hl
    omega
  · rw [he] at hK
    omega
  · have : gsum p g - 1 + 1 ≤ K := by omega
    have := hm.monotone this
    omega

theorem bp_gap_iff {b : ℕ} (hb : 1 ≤ b) :
    (¬ ∃ K, bp p K = b) ↔ ∃ g, 1 ≤ g ∧ b = gsum p g + g := by
  constructor
  · intro hno
    have hex : ∃ K, b < bp p (K + 1) := ⟨b, by
      unfold bp
      have := (gexp_spec (p := p) (b + 1)).1
      omega⟩
    set K := Nat.find hex with hKdef
    have hK : b < bp p (K + 1) := Nat.find_spec hex
    have hKle : bp p K ≤ b := by
      rcases Nat.eq_zero_or_pos K with h0 | hpos
      · rw [h0, bp_zero]
        exact hb
      · have := Nat.find_min hex (show K - 1 < K by omega)
        have e : K - 1 + 1 = K := by omega
        rw [e] at this
        omega
    have hne : bp p K ≠ b := fun h => hno ⟨K, h⟩
    have hlt : bp p K < b := by omega
    have hup : bp p (K + 1) ≤ bp p K + 2 := by
      unfold bp
      have := gexp_step (p := p) K
      omega
    have hge : gexp p (K + 1) = gexp p K + 1 := by
      unfold bp at hK hlt hup
      have := gexp_mono (p := p) K
      omega
    obtain ⟨s1, s2⟩ := gexp_spec (p := p) K
    have hnot : ¬ ((p - 1) * (K + 1 + 1) + 1 ≤ p ^ gexp p K) := by
      intro hc
      have := gexp_min (p := p) (K := K + 1) s1 hc
      omega
    refine ⟨gexp p K, s1, ?_⟩
    have hs := gsum_spec (p := p) (gexp p K)
    have hp1 := hp.out.one_lt
    have h3 : (p - 1) * (K + 1 + 1) = (p - 1) * (K + 1) + (p - 1) := by ring
    have hlo : (p - 1) * (K + 1) ≤ (p - 1) * gsum p (gexp p K) := by omega
    have hhi : (p - 1) * gsum p (gexp p K) < (p - 1) * (K + 1) + (p - 1) := by omega
    have hpp : 0 < p - 1 := by omega
    have a1 : K + 1 ≤ gsum p (gexp p K) := Nat.le_of_mul_le_mul_left hlo hpp
    have a2 : gsum p (gexp p K) < K + 1 + 1 := by
      by_contra hc
      push Not at hc
      have := Nat.mul_le_mul_left (p - 1) hc
      have e4 : (p - 1) * (K + 1 + 1) = (p - 1) * (K + 1) + (p - 1) := h3
      omega
    have hRK : gsum p (gexp p K) = K + 1 := by omega
    unfold bp at hlt hK
    omega
  · rintro ⟨g, hg, rfl⟩
    exact bp_gap_of hg

/-- Every `a` other than `(p^g - 1)/(p - 1) + g - 1` has a unique candidate. -/
theorem unique_candidate {a : ℕ} (h : ∀ g, 1 ≤ g → a + 1 ≠ gsum p g + g) :
    ∃! K, bp p K = a + 1 := by
  have : ∃ K, bp p K = a + 1 := by
    by_contra hno
    obtain ⟨g, hg, he⟩ := (bp_gap_iff (p := p) (b := a + 1) (by omega)).1 hno
    exact h g hg he
  obtain ⟨K, hK⟩ := this
  refine ⟨K, hK, ?_⟩
  intro K' hK'
  exact bp_strictMono.injective (hK'.trans hK.symm)

omit hp in
/-- Trimming the zero digits above the largest nonzero one. -/
theorem esum_trim (d : ℕ → ℕ) (K' : ℕ) (h : ∃ i, i < K' ∧ d i ≠ 0) :
    ∃ K, K < K' ∧ d K ≠ 0 ∧ esum p d K' = esum p d (K + 1) := by
  induction K' with
  | zero => obtain ⟨i, hi, _⟩ := h; omega
  | succ K' ih =>
    by_cases hd : d K' = 0
    · have h' : ∃ i, i < K' ∧ d i ≠ 0 := by
        obtain ⟨i, hi, hdi⟩ := h
        refine ⟨i, ?_, hdi⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · exact hi
        · rw [hi] at hdi; exact absurd hd hdi
      obtain ⟨K, hK, hdK, he⟩ := ih h'
      refine ⟨K, by omega, hdK, ?_⟩
      rw [esum_succ, hd, he]
      simp
    · exact ⟨K', by omega, hd, rfl⟩

/-- The exponents `a` with `a + 1 = (p^g - 1)/(p - 1) + g` are not in `𝓐_p`
(Theorem `thm:primes` (3), last statement). -/
theorem not_Ap_gap {g : ℕ} (hg : 1 ≤ g) : ¬ Ap p (gsum p g + g - 1) := by
  intro hA
  obtain ⟨K', d, hd, hnz, he⟩ := (Ap_iff _).1 hA
  obtain ⟨K, _, hK, he'⟩ := esum_trim (p := p) d K' hnz
  rw [he'] at he
  obtain ⟨hb, _⟩ := top_index hd hK he
  have hR := gsum_pos (p := p) hg
  apply bp_gap_of (p := p) hg
  refine ⟨K, ?_⟩
  unfold bp
  omega

/-- If `a ∈ 𝓐_p` then `a` has a candidate `K` with `K + g(K) = a + 1`. -/
theorem Ap_cand {a : ℕ} (hA : Ap p a) : ∃ K, bp p K = a + 1 := by
  obtain ⟨K', d, hd, hnz, he⟩ := (Ap_iff _).1 hA
  obtain ⟨K, _, hK, he'⟩ := esum_trim (p := p) d K' hnz
  rw [he'] at he
  obtain ⟨hb, _⟩ := top_index hd hK he
  exact ⟨K, by unfold bp; omega⟩

end SequenceNicolas.Primes
