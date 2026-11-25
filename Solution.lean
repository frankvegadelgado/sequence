module

public import SequenceNicolas

public section

namespace SequenceNicolas.Public

open SequenceNicolas.Core (c)
open SequenceNicolas.Recursion (hfun beta)

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
