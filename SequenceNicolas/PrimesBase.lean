module

public import Mathlib

@[expose] public section

/-!
# The analogue for an arbitrary prime: Lemma `lem:cp`

`cp p n = c_p(n) = ∑_{k=1}^{n} p^{v_p(k)}`.  The numbers `t_i = p c_p(p^i) = p^i((p-1)i + p)`
of the paper are `tt p i`; parts (2) and (3) of Lemma `lem:cp` are stated without division, as
`p c_p(p^m) = t_m`, `p c_p(p^m - 1) + p^{m+1} = t_m` and `p c_p(n) = ∑_i d_i t_i`.
-/

namespace SequenceNicolas.Primes

/-- `c_p(n) = ∑_{k=1}^n p^{v_p(k)}`. -/
noncomputable def cp (p n : ℕ) : ℕ := ∑ k ∈ Finset.range n, p ^ padicValNat p (k + 1)

/-- `t_i = p c_p(p^i) = p^i ((p-1) i + p)`. -/
def tt (p i : ℕ) : ℕ := p ^ i * ((p - 1) * i + p)

theorem cp_zero (p : ℕ) : cp p 0 = 0 := by simp [cp]

theorem cp_succ (p n : ℕ) : cp p (n + 1) = cp p n + p ^ padicValNat p (n + 1) := by
  unfold cp
  rw [Finset.sum_range_succ]

theorem pm1 {p : ℕ} (hp : 1 ≤ p) (x : ℕ) : (p - 1) * x + x = p * x := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  ring

theorem dvd_pow_sub_one (q n : ℕ) : q ∣ (q + 1) ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    have hpos : 1 ≤ (q + 1) ^ n := Nat.one_le_pow _ _ (Nat.succ_pos q)
    have h1 : (q + 1) ^ n = q * c + 1 := by omega
    refine ⟨(q + 1) * c + 1, ?_⟩
    have e : (q + 1) ^ (n + 1) = (q + 1) * (q * c + 1) := by rw [pow_succ, h1]; ring
    have e2 : (q + 1) * (q * c + 1) = q * ((q + 1) * c + 1) + 1 := by ring
    rw [e]
    exact Nat.sub_eq_of_eq_add e2

theorem sub_one_dvd_pow_sub_one (a n : ℕ) (ha : 1 ≤ a) : a - 1 ∣ a ^ n - 1 := by
  have := dvd_pow_sub_one (a - 1) n
  rwa [Nat.sub_add_cancel ha] at this

variable {p : ℕ} [hp : Fact p.Prime]

theorem p_ge_two : 2 ≤ p := hp.out.two_le

omit hp in
theorem cp_block (m : ℕ) :
    cp p (m + p) = cp p m + ∑ x ∈ Finset.range p, p ^ padicValNat p (m + x + 1) := by
  unfold cp
  rw [Finset.sum_range_add]

theorem block_sum (n : ℕ) :
    ∑ x ∈ Finset.range p, p ^ padicValNat p (p * n + x + 1) = (p - 1) + p * p ^ padicValNat p (n + 1) := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have e := Finset.sum_range_succ (fun x => p ^ padicValNat p (p * n + x + 1)) (p - 1)
  rw [Nat.sub_add_cancel hp1] at e
  rw [e]
  have h1 : ∑ x ∈ Finset.range (p - 1), p ^ padicValNat p (p * n + x + 1) = p - 1 := by
    have : ∀ x ∈ Finset.range (p - 1), p ^ padicValNat p (p * n + x + 1) = 1 := by
      intro x hx
      have hx' := Finset.mem_range.1 hx
      have hnd : ¬ p ∣ p * n + (x + 1) := by
        intro hd
        have := (Nat.dvd_add_right (dvd_mul_right p n)).1 hd
        have := Nat.le_of_dvd (by omega) this
        omega
      have : padicValNat p (p * n + x + 1) = 0 := padicValNat.eq_zero_of_not_dvd hnd
      rw [this]
      simp
    rw [Finset.sum_congr rfl this]
    simp
  have h2 : p ^ padicValNat p (p * n + (p - 1) + 1) = p * p ^ padicValNat p (n + 1) := by
    have e2 : p * n + (p - 1) + 1 = p * (n + 1) := by
      rw [mul_add, mul_one]
      omega
    rw [e2, padicValNat.mul hp.out.ne_zero (by omega), padicValNat_self, pow_add, pow_one]
  rw [h1, h2]

theorem cp_mul (n : ℕ) : cp p (p * n) = p * cp p n + (p - 1) * n := by
  induction n with
  | zero => simp [cp_zero]
  | succ n ih =>
    have e : p * (n + 1) = p * n + p := by ring
    rw [e, cp_block, block_sum, cp_succ, ih]
    ring

theorem cp_pow (m : ℕ) : p * cp p (p ^ m) = tt p m := by
  induction m with
  | zero => simp [tt, cp]
  | succ m ih =>
    have h1 : cp p (p ^ (m + 1)) = p * cp p (p ^ m) + (p - 1) * p ^ m := by
      rw [pow_succ']
      exact cp_mul _
    rw [h1]
    unfold tt at ih ⊢
    have e2 : p * (p * cp p (p ^ m) + (p - 1) * p ^ m)
        = p * (p * cp p (p ^ m)) + p * ((p - 1) * p ^ m) := mul_add _ _ _
    have e3 : p * (p * cp p (p ^ m)) = p * (p ^ m * ((p - 1) * m + p)) := by rw [← ih]
    rw [e2, e3]
    ring

theorem cp_pow_pred (m : ℕ) : p * cp p (p ^ m - 1) + p * p ^ m = tt p m := by
  have hpos : 0 < p ^ m := pow_pos hp.out.pos m
  have h1 := cp_succ p (p ^ m - 1)
  rw [Nat.sub_add_cancel hpos, padicValNat.prime_pow] at h1
  rw [← cp_pow, h1]
  ring

/-- `v_p(t p^m + k) = v_p(k)` for `1 ≤ k < p^m`. -/
theorem val_add_mul {m t k : ℕ} (hk : 1 ≤ k) (hkm : k < p ^ m) :
    padicValNat p (t * p ^ m + k) = padicValNat p k := by
  have hx : t * p ^ m + k ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  apply le_antisymm
  · have h1 : p ^ (padicValNat p (t * p ^ m + k)) ∣ t * p ^ m + k := pow_padicValNat_dvd
    set n := padicValNat p (t * p ^ m + k) with hn
    by_cases hnm : n ≤ m
    · have hd : p ^ n ∣ t * p ^ m := Dvd.dvd.mul_left (pow_dvd_pow p hnm) t
      have := (Nat.dvd_add_right hd).1 h1
      exact (padicValNat_dvd_iff_le hk0).1 this
    · exfalso
      have hmn : p ^ m ∣ p ^ n := pow_dvd_pow p (by omega)
      have h2 : p ^ m ∣ t * p ^ m + k := dvd_trans hmn h1
      have hd : p ^ m ∣ t * p ^ m := Dvd.intro_left t rfl
      have := (Nat.dvd_add_right hd).1 h2
      have := Nat.le_of_dvd (by omega) this
      omega
  · have h1 : p ^ (padicValNat p k) ∣ k := pow_padicValNat_dvd
    set n := padicValNat p k with hn
    have hnm : n ≤ m := by
      by_contra hc
      have hmn : p ^ m ∣ p ^ n := pow_dvd_pow p (by omega)
      have := Nat.le_of_dvd (by omega) (dvd_trans hmn h1)
      omega
    have hd : p ^ n ∣ t * p ^ m := Dvd.dvd.mul_left (pow_dvd_pow p hnm) t
    exact (padicValNat_dvd_iff_le hx).1 (dvd_add hd h1)

/-- `c_p(x p^m + s) = c_p(x p^m) + c_p(s)` for `s < p^m`. -/
theorem cp_add_low {m t s : ℕ} (hs : s < p ^ m) :
    cp p (t * p ^ m + s) = cp p (t * p ^ m) + cp p s := by
  unfold cp
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.1 hj
  have h := val_add_mul (p := p) (m := m) (t := t) (k := j + 1) (by omega) (by omega)
  rw [← add_assoc] at h
  rw [h]

theorem cp_mul_pow {m : ℕ} (t : ℕ) (ht : t ≤ p - 1) : cp p (t * p ^ m) = t * cp p (p ^ m) := by
  induction t with
  | zero => simp [cp_zero]
  | succ t ih =>
    have ih' := ih (by omega)
    have hpos : 0 < p ^ m := pow_pos hp.out.pos m
    have e : (t + 1) * p ^ m = t * p ^ m + p ^ m := by ring
    rw [e]
    unfold cp at ih' ⊢
    rw [Finset.sum_range_add]
    have hlow : ∑ x ∈ Finset.range (p ^ m - 1), p ^ padicValNat p (t * p ^ m + x + 1) =
        ∑ k ∈ Finset.range (p ^ m - 1), p ^ padicValNat p (k + 1) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hx' := Finset.mem_range.1 hx
      have := val_add_mul (p := p) (m := m) (t := t) (k := x + 1) (by omega) (by omega)
      rw [← add_assoc] at this
      rw [this]
    have hr : p ^ m = (p ^ m - 1) + 1 := by omega
    have hsplit := Finset.sum_range_succ (fun x => p ^ padicValNat p (t * p ^ m + x + 1)) (p ^ m - 1)
    rw [← hr] at hsplit
    have hlast : p ^ padicValNat p (t * p ^ m + (p ^ m - 1) + 1) = p ^ m := by
      have e2 : t * p ^ m + (p ^ m - 1) + 1 = (t + 1) * p ^ m := by
        rw [add_mul, one_mul]
        omega
      have hnd : ¬ p ∣ t + 1 := by
        intro hd
        have := Nat.le_of_dvd (by omega) hd
        omega
      rw [e2, padicValNat.mul (by omega) (pow_ne_zero m hp.out.ne_zero),
        padicValNat.eq_zero_of_not_dvd hnd, padicValNat.prime_pow]
      simp
    have hc : ∑ k ∈ Finset.range (p ^ m), p ^ padicValNat p (k + 1) =
        ∑ k ∈ Finset.range (p ^ m - 1), p ^ padicValNat p (k + 1) + p ^ m := by
      have := Finset.sum_range_succ (fun k => p ^ padicValNat p (k + 1)) (p ^ m - 1)
      rw [← hr] at this
      rw [this, padicValNat.prime_pow]
    rw [hsplit, hlast, hlow]
    rw [add_mul, one_mul, ← hc]
    omega

/-- `c_p(d p^m + s) = d c_p(p^m) + c_p(s)` for `d ≤ p - 1` and `s < p^m`. -/
theorem cp_digit {m d s : ℕ} (hd : d ≤ p - 1) (hs : s < p ^ m) :
    cp p (d * p ^ m + s) = d * cp p (p ^ m) + cp p s := by
  rw [cp_add_low hs, cp_mul_pow d hd]

/-- The value `∑_{i<K} d_i p^i`. -/
def dval (p : ℕ) (d : ℕ → ℕ) (K : ℕ) : ℕ := ∑ i ∈ Finset.range K, d i * p ^ i

/-- The sum `∑_{i<K} d_i t_i`. -/
def esum (p : ℕ) (d : ℕ → ℕ) (K : ℕ) : ℕ := ∑ i ∈ Finset.range K, d i * tt p i

theorem dval_lt {d : ℕ → ℕ} (hd : ∀ i, d i ≤ p - 1) (K : ℕ) : dval p d K < p ^ K := by
  induction K with
  | zero => simp [dval]
  | succ K ih =>
    have h1 : dval p d (K + 1) = dval p d K + d K * p ^ K := by
      unfold dval
      rw [Finset.sum_range_succ]
    have h2 : d K * p ^ K ≤ (p - 1) * p ^ K := Nat.mul_le_mul_right _ (hd K)
    have h3 := pm1 hp.out.one_lt.le (p ^ K)
    have h4 : p ^ (K + 1) = p * p ^ K := by ring
    omega

/-- Lemma `lem:cp` (3): `p c_p(∑ d_i p^i) = ∑ d_i t_i`. -/
theorem cp_digits {d : ℕ → ℕ} (hd : ∀ i, d i ≤ p - 1) (K : ℕ) :
    p * cp p (dval p d K) = esum p d K := by
  induction K with
  | zero => simp [dval, esum, cp_zero]
  | succ K ih =>
    have h1 : dval p d (K + 1) = d K * p ^ K + dval p d K := by
      unfold dval
      rw [Finset.sum_range_succ, add_comm]
    have h2 : esum p d (K + 1) = esum p d K + d K * tt p K := by
      unfold esum
      rw [Finset.sum_range_succ]
    rw [h1, cp_digit (hd K) (dval_lt hd K), h2, ← ih, ← cp_pow]
    ring

end SequenceNicolas.Primes
