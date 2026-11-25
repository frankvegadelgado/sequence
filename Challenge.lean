module

public import Mathlib

@[expose] public section

/-!
# Canonical standalone challenge

This file intentionally imports only Mathlib so Palomar can compile it in an
isolated canonical environment. The implementation lives in the project
modules imported by `Solution.lean`.
-/

namespace SequenceNicolas.Core

/-- `c n = ∑_{k = 1}^{n} 2 ^ {v_2 k}`, the function of Nicolas's question
(equation `eq:cdef` of the paper); `v_2` is the `2`-adic valuation. -/
def c (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, 2 ^ padicValNat 2 k

theorem c_zero : c 0 = 0 := by
  rfl

theorem c_succ (n : ℕ) : c (n + 1) = c n + 2 ^ padicValNat 2 (n + 1) := by
  unfold c
  exact Finset.sum_Icc_succ_top (by omega) _

theorem c_one : c 1 = 1 := by
  have h := c_succ 0
  simp [c_zero] at h
  exact h

theorem v_two_mul {m : ℕ} (hm : m ≠ 0) :
    padicValNat 2 (2 * m) = padicValNat 2 m + 1 := by
  rw [padicValNat.mul (p := 2) (show (2 : ℕ) ≠ 0 by norm_num) hm]
  have h2 : padicValNat 2 2 = 1 := by
    exact padicValNat_self
  omega

theorem v_odd (m : ℕ) : padicValNat 2 (2 * m + 1) = 0 :=
  padicValNat.eq_zero_of_not_dvd (by omega)

/-- The recurrence `c(2n) = 2 c(n) + n`. -/
theorem c_double (n : ℕ) : c (2 * n) = 2 * c n + n := by
  induction n with
  | zero => simp [c_zero]
  | succ n ih =>
    have e : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    have a := c_succ (2 * n)
    have b := c_succ (2 * n + 1)
    have hv1 : padicValNat 2 (2 * n + 1) = 0 := v_odd n
    have hv2 : padicValNat 2 (2 * n + 1 + 1) = padicValNat 2 (n + 1) + 1 := by
      have e2 : 2 * n + 1 + 1 = 2 * (n + 1) := by ring
      rw [e2]
      exact v_two_mul (Nat.succ_ne_zero n)
    rw [e, b, a, ih, c_succ n, hv1, hv2]; ring

/-- The recurrence `c(2n + 1) = 2 c(n) + n + 1`. -/
theorem c_double_succ (n : ℕ) : c (2 * n + 1) = 2 * c n + n + 1 := by
  have h1 := c_succ (2 * n)
  rw [v_odd, pow_zero] at h1
  have h2 := c_double n
  omega

/-- Lemma `lem:cformula`: `2 c(2^r) = 2^r (r + 2)`, that is `c(2^r) = 2^{r-1}(r+2)`. -/
theorem two_mul_c_pow (r : ℕ) : 2 * c (2 ^ r) = 2 ^ r * (r + 2) := by
  induction r with
  | zero =>
    simp [c_one]
  | succ r ih =>
    have h2 : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
    have h : c (2 ^ (r + 1)) = 2 * c (2 ^ r) + 2 ^ r := by
      rw [h2]
      exact c_double _
    rw [h]
    have key : 2 * (2 * c (2 ^ r) + 2 ^ r) = 2 * (2 * c (2 ^ r)) + 2 * 2 ^ r := by ring
    rw [key, ih]; ring

/-- `c(2^m + s) = c(2^m) + c(s)` for `s < 2^m` (proof of Lemma `lem:cformula`). -/
theorem c_add_pow (a : ℕ) : ∀ t : ℕ, t < 2 ^ a → c (2 ^ a + t) = c (2 ^ a) + c t := by
  induction a with
  | zero =>
    intro t ht
    have h0 : t = 0 := by simpa using ht
    subst h0
    simp [c_zero]
  | succ a ih =>
    intro t ht
    have h2 : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
    have ht2 : t < 2 * 2 ^ a := by rw [h2] at ht; exact ht
    obtain ⟨t', e, he, rfl⟩ : ∃ t' e : ℕ, e < 2 ∧ t = 2 * t' + e :=
      ⟨t / 2, t % 2, by omega, by omega⟩
    have ht' : t' < 2 ^ a := by omega
    have hB : c (2 ^ (a + 1)) = 2 * c (2 ^ a) + 2 ^ a := by
      rw [h2]
      exact c_double _
    have hI := ih t' ht'
    rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
    · have h1 : 2 ^ (a + 1) + (2 * t' + 0) = 2 * (2 ^ a + t') := by ring
      have hA : c (2 ^ (a + 1) + (2 * t' + 0)) = 2 * c (2 ^ a + t') + (2 ^ a + t') := by
        rw [h1]
        exact c_double _
      have hC : c (2 * t' + 0) = 2 * c t' + t' := by
        rw [Nat.add_zero]
        exact c_double t'
      rw [hA, hB, hC, hI]; ring
    · have h1 : 2 ^ (a + 1) + (2 * t' + 1) = 2 * (2 ^ a + t') + 1 := by ring
      have hA : c (2 ^ (a + 1) + (2 * t' + 1)) = 2 * c (2 ^ a + t') + (2 ^ a + t') + 1 := by
        rw [h1]
        exact c_double_succ _
      have hC : c (2 * t' + 1) = 2 * c t' + t' + 1 := c_double_succ t'
      rw [hA, hB, hC, hI]; ring

theorem geom_two (a : ℕ) : ∑ i ∈ Finset.range a, 2 ^ i + 1 = 2 ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

theorem sum_pow_lt {s : Finset ℕ} {a : ℕ} (hs : ∀ x ∈ s, x < a) :
    ∑ i ∈ s, 2 ^ i < 2 ^ a := by
  have h1 : ∑ i ∈ s, 2 ^ i ≤ ∑ i ∈ Finset.range a, 2 ^ i :=
    Finset.sum_le_sum_of_subset (fun x hx => Finset.mem_range.2 (hs x hx))
  have h2 := geom_two a
  omega

/-- Every natural number is a sum of distinct powers of two. -/
theorem exists_pow_sum (n : ℕ) : ∃ S : Finset ℕ, ∑ i ∈ S, 2 ^ i = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨∅, by simp⟩
    · have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
      have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn0
      have h2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
      generalize Nat.log 2 n = m at h1 h2
      have h2' : n < 2 ^ m * 2 := by rw [pow_succ] at h2; exact h2
      have hpos : 0 < 2 ^ m := by positivity
      have h3 : n - 2 ^ m < n := by omega
      obtain ⟨S', hS'⟩ := ih (n - 2 ^ m) h3
      have hlt : ∀ i ∈ S', i < m := by
        intro i hi
        by_contra hcon
        push Not at hcon
        have h4 : 2 ^ i ≤ ∑ j ∈ S', 2 ^ j :=
          Finset.single_le_sum (f := fun j => 2 ^ j) (fun _ _ => Nat.zero_le _) hi
        have h5 : 2 ^ m ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hcon
        omega
      refine ⟨insert m S', ?_⟩
      rw [Finset.sum_insert (fun h => lt_irrefl m (hlt m h)), hS']
      omega

/-- Formula `eq:cformula` of Lemma `lem:cformula` in the form
`2 c(n) = 2 n + ∑_{i ∈ B(n)} i 2^i`, for `n = ∑_{i ∈ S} 2^i` with `S = B(n)`. -/
theorem two_mul_c_sum (S : Finset ℕ) :
    2 * c (∑ i ∈ S, 2 ^ i) = 2 * (∑ i ∈ S, 2 ^ i) + ∑ i ∈ S, i * 2 ^ i := by
  refine Finset.induction_on_max S ?_ ?_
  · simp [c_zero]
  · intro a s hs ih
    have ha : a ∉ s := fun h => lt_irrefl a (hs a h)
    have hlt : ∑ i ∈ s, 2 ^ i < 2 ^ a := sum_pow_lt hs
    rw [Finset.sum_insert ha, Finset.sum_insert ha, c_add_pow a _ hlt]
    have h2 := two_mul_c_pow a
    nlinarith [ih, h2]

/-- `8 c(n) = ∑_{j ∈ B(n) + 2} j 2^j` (proof of Theorem `thm:equiv`). -/
theorem eight_mul_c (S : Finset ℕ) :
    8 * c (∑ i ∈ S, 2 ^ i) = ∑ i ∈ S, (i + 2) * 2 ^ (i + 2) := by
  have h := two_mul_c_sum S
  have e : ∑ i ∈ S, (i + 2) * 2 ^ (i + 2) =
      4 * ∑ i ∈ S, i * 2 ^ i + 8 * ∑ i ∈ S, 2 ^ i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [e]
  omega

/-- Theorem `thm:equiv`, second statement: `1 ∉ T`. -/
theorem repr_no_one {T : Finset ℕ} (hT : ∀ j ∈ T, 1 ≤ j) {a : ℕ}
    (hsum : ∑ j ∈ T, j * 2 ^ j = 2 ^ (a + 3)) : 1 ∉ T := by
  intro h1
  have hdiv : 8 ∣ ∑ j ∈ T.erase 1, j * 2 ^ j := by
    apply Finset.dvd_sum
    intro j hj
    have hj1 : j ≠ 1 := (Finset.mem_erase.1 hj).1
    have hj2 : 1 ≤ j := hT j (Finset.mem_erase.1 hj).2
    rcases (by omega : j = 2 ∨ 3 ≤ j) with rfl | h3
    · norm_num
    · have h : 2 ^ 3 ∣ 2 ^ j := pow_dvd_pow 2 h3
      have h8 : (8 : ℕ) ∣ 2 ^ j := by
        exact h
      exact Dvd.dvd.mul_left h8 j
  have hsplit := Finset.add_sum_erase T (fun j => j * 2 ^ j) h1
  have h8 : 8 ∣ 2 ^ (a + 3) := ⟨2 ^ a, by ring⟩
  simp only [one_mul, pow_one] at hsplit
  omega

/-- Theorem `thm:equiv`: `2^a` is in the image of `c` if and only if `2^(a+3)` is a sum
`∑_{j ∈ T} j 2^j` over a finite set `T` of positive integers. -/
theorem equiv_repr (a : ℕ) :
    (∃ n : ℕ, c n = 2 ^ a) ↔
      ∃ T : Finset ℕ, (∀ j ∈ T, 1 ≤ j) ∧ ∑ j ∈ T, j * 2 ^ j = 2 ^ (a + 3) := by
  have e8 : (2 : ℕ) ^ (a + 3) = 8 * 2 ^ a := by ring
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨S, hS⟩ := exists_pow_sum n
    have h8 := eight_mul_c S
    rw [hS, hn] at h8
    refine ⟨S.map (addRightEmbedding 2), ?_, ?_⟩
    · intro j hj
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 hj
      show 1 ≤ i + 2
      omega
    · rw [Finset.sum_map]
      show ∑ i ∈ S, (i + 2) * 2 ^ (i + 2) = 2 ^ (a + 3)
      rw [e8]
      exact h8.symm
  · rintro ⟨T, hT, hsum⟩
    have h1 := repr_no_one hT hsum
    have h2 : ∀ j ∈ T, 2 ≤ j := by
      intro j hj
      have := hT j hj
      rcases (by omega : j = 1 ∨ 2 ≤ j) with rfl | h
      · exact absurd hj h1
      · exact h
    refine ⟨∑ i ∈ T.image (fun j => j - 2), 2 ^ i, ?_⟩
    have hinj : Set.InjOn (fun j => j - 2) (T : Set ℕ) := by
      intro x hx y hy hxy
      have hx2 := h2 x hx
      have hy2 := h2 y hy
      have hxy' : x - 2 = y - 2 := hxy
      omega
    have h8 := eight_mul_c (T.image (fun j => j - 2))
    have e : ∑ i ∈ T.image (fun j => j - 2), (i + 2) * 2 ^ (i + 2) =
        ∑ j ∈ T, j * 2 ^ j := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hj2 := h2 j hj
      have hj3 : j - 2 + 2 = j := by omega
      show (j - 2 + 2) * 2 ^ (j - 2 + 2) = j * 2 ^ j
      rw [hj3]
    rw [e, hsum, e8] at h8
    omega

/-- Lemma `lem:sum`: `∑_{j = 1}^{J} j 2^j = (J - 1) 2^{J+1} + 2`, written without subtraction. -/
theorem sum_j_two_pow (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, j * 2 ^ j + 2 ^ (J + 1) = J * 2 ^ (J + 1) + 2 := by
  induction J with
  | zero =>
    simp
  | succ J ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ J + 1 by omega)]
    have hX : 2 ^ (J + 1 + 1) = 2 * 2 ^ (J + 1) := by ring
    rw [hX]
    nlinarith [ih]

/-- Theorem `thm:leading` (1): if `T` is a finite set of positive integers with maximum `K`
and `∑_{j ∈ T} j 2^j = 2^b`, `b ≥ 3`, then `K ≥ 2` and `b = K + ⌈log₂ K⌉`; the integer
`g = ⌈log₂ K⌉` is characterised by `K ≤ 2^g < 2 K`. -/
theorem leading_term {T : Finset ℕ} (hT : ∀ j ∈ T, 1 ≤ j) {b K : ℕ} (hb : 3 ≤ b)
    (hK : K ∈ T) (hmax : ∀ j ∈ T, j ≤ K) (hsum : ∑ j ∈ T, j * 2 ^ j = 2 ^ b) :
    2 ≤ K ∧ ∃ g : ℕ, K ≤ 2 ^ g ∧ 2 ^ g < 2 * K ∧ b = K + g := by
  have hK1 : 1 ≤ K := hT K hK
  have hlow : K * 2 ^ K ≤ 2 ^ b := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun j => j * 2 ^ j) (fun _ _ => Nat.zero_le _) hK
  have hsub : T ⊆ Finset.Icc 1 K := fun j hj => Finset.mem_Icc.2 ⟨hT j hj, hmax j hj⟩
  have hup0 : ∑ j ∈ T, j * 2 ^ j ≤ ∑ j ∈ Finset.Icc 1 K, j * 2 ^ j :=
    Finset.sum_le_sum_of_subset hsub
  have hS := sum_j_two_pow K
  have hX2 : 2 ^ (K + 1) = 2 * 2 ^ K := by ring
  have hupper : 2 ^ b + 2 ^ (K + 1) ≤ K * 2 ^ (K + 1) + 2 := by
    linarith [hsum, hup0, hS]
  have h8 : 8 ≤ 2 ^ b := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hK2 : 2 ≤ K := by
    by_contra hc
    have hK1' : K = 1 := by omega
    rw [hK1'] at hupper
    have h4 : (2 : ℕ) ^ (1 + 1) = 4 := by norm_num
    rw [h4] at hupper
    omega
  have hbK : K ≤ b := by
    by_contra hc
    push Not at hc
    have h1 : 2 ^ b < 2 ^ K := by
      exact Nat.pow_lt_pow_right (by norm_num) hc
    have h2 : 2 ^ K ≤ K * 2 ^ K := by
      exact Nat.le_mul_of_pos_left _ (by omega)
    omega
  obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_le hbK
  have hpow : 2 ^ (K + g) = 2 ^ K * 2 ^ g := pow_add 2 K g
  have hp : 0 < 2 ^ K := by positivity
  refine ⟨hK2, g, ?_, ?_, rfl⟩
  · by_contra hc
    push Not at hc
    have h1 : (2 ^ g + 1) * 2 ^ K ≤ K * 2 ^ K := Nat.mul_le_mul_right _ (by omega)
    rw [hpow] at hlow
    nlinarith [hlow, h1, hp]
  · by_contra hc
    push Not at hc
    have h4 : 4 ≤ 2 ^ K := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK2
    have h5 : 2 ^ K * (2 * K) ≤ 2 ^ K * 2 ^ g := Nat.mul_le_mul_left _ hc
    rw [hpow, hX2] at hupper
    nlinarith [hupper, h5, h4]

/-- Theorem `thm:members` (1): `c(2^{2^r - 2}) = 2^{2^r + r - 3}`, written as
`8 c(2^{2^r - 2}) = 2^{2^r + r}`. -/
theorem members_one (r : ℕ) (hr : 1 ≤ r) :
    8 * c (2 ^ (2 ^ r - 2)) = 2 ^ (2 ^ r + r) := by
  have h2 : 2 ≤ 2 ^ r := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  obtain ⟨m, hm2⟩ : ∃ m : ℕ, m + 2 = 2 ^ r := ⟨2 ^ r - 2, by omega⟩
  have hm' : 2 ^ r - 2 = m := by omega
  have e : 2 ^ r + r = m + r + 2 := by omega
  have key := two_mul_c_pow m
  rw [hm2] at key
  rw [hm', e]
  calc 8 * c (2 ^ m) = 4 * (2 * c (2 ^ m)) := by ring
    _ = 4 * (2 ^ m * 2 ^ r) := by rw [key]
    _ = 2 ^ (m + r + 2) := by ring

/-- Theorem `thm:members` (2), identity `eq:member`: if `K (2^s + 1) = 2^(h+s) + s` and
`s + 2 ≤ K`, then `c(2^{K-2} + 2^{K-s-2}) = 2^{K+h-3}`, written as
`8 c(2^{K-2} + 2^{K-s-2}) = 2^{K+h}`. -/
theorem members_two {s h K : ℕ} (hs : 1 ≤ s) (hKs : s + 2 ≤ K)
    (hKeq : K * (2 ^ s + 1) = 2 ^ (h + s) + s) :
    8 * c (2 ^ (K - 2) + 2 ^ (K - s - 2)) = 2 ^ (K + h) := by
  obtain ⟨u, rfl⟩ : ∃ u : ℕ, K = u + s + 2 := ⟨K - s - 2, by omega⟩
  have e1 : u + s + 2 - 2 = u + s := by omega
  have e2 : u + s + 2 - s - 2 = u := by omega
  rw [e1, e2]
  have hlt : 2 ^ u < 2 ^ (u + s) := by
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [c_add_pow (u + s) _ hlt]
  have hA := two_mul_c_pow (u + s)
  have hB := two_mul_c_pow u
  have hpow : 2 ^ (h + s) = 2 ^ h * 2 ^ s := pow_add 2 h s
  rw [hpow] at hKeq
  have hY : (u + s + 2) * 2 ^ s + (u + 2) = 2 ^ h * 2 ^ s := by
    nlinarith [hKeq]
  calc 8 * (c (2 ^ (u + s)) + c (2 ^ u))
      = 4 * (2 * c (2 ^ (u + s)) + 2 * c (2 ^ u)) := by ring
    _ = 4 * (2 ^ (u + s) * (u + s + 2) + 2 ^ u * (u + 2)) := by rw [hA, hB]
    _ = 4 * (2 ^ u * ((u + s + 2) * 2 ^ s + (u + 2))) := by ring
    _ = 4 * (2 ^ u * (2 ^ h * 2 ^ s)) := by rw [hY]
    _ = 2 ^ (u + s + 2 + h) := by ring

/-- Theorem `thm:members` (2): `2^{h-1} < K < 2^h`, written as `2^h < 2 K` and `K < 2^h`,
so that `h = ⌈log₂ K⌉`. -/
theorem members_two_bounds {s h K : ℕ} (hs : 1 ≤ s) (hsh : s < 2 ^ h)
    (hKeq : K * (2 ^ s + 1) = 2 ^ (h + s) + s) : K < 2 ^ h ∧ 2 ^ h < 2 * K := by
  have hpow : 2 ^ (h + s) = 2 ^ h * 2 ^ s := pow_add 2 h s
  rw [hpow] at hKeq
  have hp : 0 < 2 ^ h := by positivity
  have h2s : 2 ≤ 2 ^ s := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  constructor
  · by_contra hc
    push Not at hc
    have h1 : 2 ^ h * (2 ^ s + 1) ≤ K * (2 ^ s + 1) := Nat.mul_le_mul_right _ hc
    nlinarith [h1, hKeq, hsh]
  · by_contra hc
    push Not at hc
    have h1 : 2 * K * (2 ^ s + 1) ≤ 2 ^ h * (2 ^ s + 1) := Nat.mul_le_mul_right _ hc
    have h2 : 2 ^ h * 2 ≤ 2 ^ h * 2 ^ s := Nat.mul_le_mul_left _ h2s
    nlinarith [h1, h2, hKeq, hp]

end SequenceNicolas.Core

namespace SequenceNicolas.Recursion

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

end SequenceNicolas.Recursion

namespace SequenceNicolas.Public

open SequenceNicolas.Core (c)

theorem c_double (n : ℕ) : c (2 * n) = 2 * c n + n :=
  SequenceNicolas.Core.c_double n

theorem c_double_succ (n : ℕ) : c (2 * n + 1) = 2 * c n + n + 1 :=
  SequenceNicolas.Core.c_double_succ n

theorem two_mul_c_pow (r : ℕ) : 2 * c (2 ^ r) = 2 ^ r * (r + 2) :=
  SequenceNicolas.Core.two_mul_c_pow r

theorem c_add_pow (a t : ℕ) (ht : t < 2 ^ a) : c (2 ^ a + t) = c (2 ^ a) + c t :=
  SequenceNicolas.Core.c_add_pow a t ht

theorem exists_pow_sum (n : ℕ) : ∃ S : Finset ℕ, ∑ i ∈ S, 2 ^ i = n :=
  SequenceNicolas.Core.exists_pow_sum n

theorem two_mul_c_sum (S : Finset ℕ) :
    2 * c (∑ i ∈ S, 2 ^ i) = 2 * (∑ i ∈ S, 2 ^ i) + ∑ i ∈ S, i * 2 ^ i :=
  SequenceNicolas.Core.two_mul_c_sum S

theorem eight_mul_c (S : Finset ℕ) :
    8 * c (∑ i ∈ S, 2 ^ i) = ∑ i ∈ S, (i + 2) * 2 ^ (i + 2) :=
  SequenceNicolas.Core.eight_mul_c S

theorem repr_no_one {T : Finset ℕ} (hT : ∀ j ∈ T, 1 ≤ j) {a : ℕ}
    (hsum : ∑ j ∈ T, j * 2 ^ j = 2 ^ (a + 3)) : 1 ∉ T :=
  SequenceNicolas.Core.repr_no_one hT hsum

theorem equiv_repr (a : ℕ) :
    (∃ n : ℕ, c n = 2 ^ a) ↔
      ∃ T : Finset ℕ, (∀ j ∈ T, 1 ≤ j) ∧ ∑ j ∈ T, j * 2 ^ j = 2 ^ (a + 3) :=
  SequenceNicolas.Core.equiv_repr a

theorem sum_j_two_pow (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, j * 2 ^ j + 2 ^ (J + 1) = J * 2 ^ (J + 1) + 2 :=
  SequenceNicolas.Core.sum_j_two_pow J

theorem leading_term {T : Finset ℕ} (hT : ∀ j ∈ T, 1 ≤ j) {b K : ℕ} (hb : 3 ≤ b)
    (hK : K ∈ T) (hmax : ∀ j ∈ T, j ≤ K) (hsum : ∑ j ∈ T, j * 2 ^ j = 2 ^ b) :
    2 ≤ K ∧ ∃ g : ℕ, K ≤ 2 ^ g ∧ 2 ^ g < 2 * K ∧ b = K + g :=
  SequenceNicolas.Core.leading_term hT hb hK hmax hsum

theorem members_one (r : ℕ) (hr : 1 ≤ r) :
    8 * c (2 ^ (2 ^ r - 2)) = 2 ^ (2 ^ r + r) :=
  SequenceNicolas.Core.members_one r hr

theorem members_two {s h K : ℕ} (hs : 1 ≤ s) (hKs : s + 2 ≤ K)
    (hKeq : K * (2 ^ s + 1) = 2 ^ (h + s) + s) :
    8 * c (2 ^ (K - 2) + 2 ^ (K - s - 2)) = 2 ^ (K + h) :=
  SequenceNicolas.Core.members_two hs hKs hKeq

theorem members_two_bounds {s h K : ℕ} (hs : 1 ≤ s) (hsh : s < 2 ^ h)
    (hKeq : K * (2 ^ s + 1) = 2 ^ (h + s) + s) : K < 2 ^ h ∧ 2 ^ h < 2 * K :=
  SequenceNicolas.Core.members_two_bounds hs hsh hKeq


open SequenceNicolas.Recursion (hfun beta)

theorem hfun_spec {K : ℕ} (hK : 2 ≤ K) :
    1 ≤ hfun K ∧ K ≤ 2 ^ hfun K ∧ 2 ^ hfun K < 2 * K :=
  SequenceNicolas.Recursion.hfun_spec hK

theorem hfun_of_bounds {K g : ℕ} (hK : 2 ≤ K) (h1 : K ≤ 2 ^ g) (h2 : 2 ^ g < 2 * K) :
    hfun K = g :=
  SequenceNicolas.Recursion.hfun_of_bounds hK h1 h2

theorem hfun_succ (K : ℕ) :
    hfun (K + 1) = hfun K ∨ (K = 2 ^ hfun K ∧ hfun (K + 1) = hfun K + 1) :=
  SequenceNicolas.Recursion.hfun_succ K

theorem beta_strictMono : StrictMono beta :=
  SequenceNicolas.Recursion.beta_strictMono

theorem beta_two_pow {r : ℕ} (hr : 1 ≤ r) : beta (2 ^ r) = 2 ^ r + r :=
  SequenceNicolas.Recursion.beta_two_pow hr

theorem beta_two_pow_succ {r : ℕ} : beta (2 ^ r + 1) = 2 ^ r + r + 2 :=
  SequenceNicolas.Recursion.beta_two_pow_succ

end SequenceNicolas.Public
