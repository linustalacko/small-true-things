/-
A056240: the smallest number whose prime factors (with multiplicity) add up to n.

The OEIS entry carries this comment (David James Sycamore and Michel Marcus, June 2017):

  For even composite n, let P_n denote the largest prime < n-1 such that n-P_n is prime
  (except if n = 6).
  For odd composite n, let P_n denote the largest prime < n-1 such that n-3-P_n is prime.
  Conjecture: a(n) = min { q*a(n-q); q prime, P_n <= q < n-1 }.

`A056240.sycamore_marcus` proves it for any `a` that is the entry's definition: `sopfr (a n) = n`,
and `a n ≤ m` for every `m` whose prime factors add up to `n`. The statement takes `P_n` as a
hypothesis (`IsGreatest`), so it assumes nothing about Goldbach's conjecture: it holds for every
composite `n ≠ 6` that has a `P_n`. `A056240.a0` is a concrete `a` meeting the hypotheses.

The idea: `a n = q * a (n - q)` for every prime factor `q` of `a n`, so it is enough that some prime
factor of `a n` is at least `P_n`. If none were, the product bounds `prod_ge_mul` (integers of sum
`P + r`, none above `P`, multiply to at least `P * r`) show `a n ≥ P * (n - P)` (n even) or
`a n ≥ 3 * P * (n - 3 - P)` (n odd), and those numbers have prime factors adding to `n`, so `a n`
would equal one of them, which has the factor `P`.
-/
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic

namespace A056240

/-- Sum of the prime factors of `m`, with multiplicity (A001414). -/
def sopfr (m : ℕ) : ℕ := m.primeFactorsList.sum

theorem sopfr_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : sopfr (a * b) = sopfr a + sopfr b := by
  unfold sopfr
  rw [(Nat.perm_primeFactorsList_mul ha hb).sum_eq, List.sum_append]

theorem sopfr_prime {p : ℕ} (hp : p.Prime) : sopfr p = p := by
  simp [sopfr, Nat.primeFactorsList_prime hp]

theorem sopfr_zero : sopfr 0 = 0 := by simp [sopfr]

theorem sopfr_one : sopfr 1 = 0 := by simp [sopfr]

/-! ### Products of integers at least 2 -/

/-- Integers that are all at least 2 multiply to at least their sum. -/
theorem sum_le_prod : ∀ L : List ℕ, (∀ a ∈ L, 2 ≤ a) → L.sum ≤ L.prod
  | [], _ => by simp
  | x :: L, h => by
    simp only [List.sum_cons, List.prod_cons]
    have hx := h x (by simp)
    have ih := sum_le_prod L (fun a ha => h a (by simp [ha]))
    rcases L with _ | ⟨y, L⟩
    · simp
    · have hy := h y (by simp)
      have : 2 ≤ (y :: L).sum := by simp; omega
      nlinarith

/-- Greedy split: a list whose sum reaches `r > 0` has a first element at which its running sum
reaches `r`. -/
theorem split : ∀ (L : List ℕ) (r : ℕ), 0 < r → r ≤ L.sum →
    ∃ L1 z L2, L = L1 ++ z :: L2 ∧ L1.sum < r ∧ r ≤ L1.sum + z
  | [], r, hr, h => by simp at h; omega
  | x :: L, r, hr, h => by
    by_cases hx : r ≤ x
    · exact ⟨[], x, L, by simp, by simp; omega, by simpa using hx⟩
    · obtain ⟨L1, z, L2, hL, h1, h2⟩ := split L (r - x) (by omega) (by simp at h; omega)
      exact ⟨x :: L1, z, L2, by simp [hL], by simp; omega, by simp; omega⟩

/-- Three numbers, each below `r`, with sum `P + r`, two of them adding to more than `P`, multiply
to at least `P * r`. -/
theorem three_groups (A Z C P r : ℕ) (hA : A < r) (hZ : Z < r) (hS : A + Z + C = P + r)
    (hg : P < A + Z) (hrP : r ≤ P) (hP : 5 ≤ P) : P * r ≤ A * Z * C := by
  have hr4 : 4 ≤ r := by omega
  zify at hA hZ hS hg hrP hP hr4 ⊢
  have hC : (C : ℤ) ≤ (r : ℤ) - 1 := by linarith
  set M : ℤ := (r : ℤ) - 1
  have hAM : (A : ℤ) ≤ M := by omega
  have hZM : (Z : ℤ) ≤ M := by omega
  have hM0 : 0 ≤ M := by omega
  have hC0 : (0 : ℤ) ≤ C := by positivity
  have e1 : M * (A + Z - M) ≤ A * Z := by
    nlinarith [mul_nonneg (sub_nonneg.2 hAM) (sub_nonneg.2 hZM)]
  have e2 : M * M * (A + Z + C - 2 * M) ≤ M * (A + Z - M) * C := by
    nlinarith [mul_nonneg hM0 (mul_nonneg (by omega : (0:ℤ) ≤ 2 * M - A - Z) (sub_nonneg.2 hC))]
  have e3 : M * (A + Z - M) * C ≤ A * Z * C := mul_le_mul_of_nonneg_right e1 hC0
  have e4 : (P : ℤ) * r ≤ M * M * (A + Z + C - 2 * M) := by
    have hs : (A : ℤ) + Z + C - 2 * M = (P : ℤ) - r + 2 := by omega
    rw [hs]
    have h1 : (0 : ℤ) ≤ (r : ℤ) - 4 := by omega
    have h2 : (0 : ℤ) ≤ (P : ℤ) - r := by omega
    nlinarith [mul_nonneg h1 h2, mul_nonneg (mul_nonneg h1 h1) h2, mul_nonneg h1 h1]
  linarith

/-- Three numbers, each at least `r + 2`, with sum `P + r + 3`, multiply to at least `3 * P * r`. -/
theorem three_large (U V C P r : ℕ) (hU : r + 2 ≤ U) (hV : r + 2 ≤ V) (hC : r + 2 ≤ C)
    (hS : U + V + C = P + r + 3) : 3 * P * r ≤ U * V * C := by
  zify at hU hV hC hS ⊢
  set M : ℤ := (r : ℤ) + 2
  have e1 : M * ((U : ℤ) + V - M) ≤ (U : ℤ) * V := by
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ U - M) (by omega : (0 : ℤ) ≤ V - M)]
  have e2 : M * M * ((U : ℤ) + V + C - 2 * M) ≤ M * ((U : ℤ) + V - M) * C := by
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ M)
      (mul_nonneg (by omega : (0 : ℤ) ≤ U + V - 2 * M) (by omega : (0 : ℤ) ≤ C - M))]
  have e3 : M * ((U : ℤ) + V - M) * C ≤ (U : ℤ) * V * C :=
    mul_le_mul_of_nonneg_right e1 (by omega)
  have e4 : 3 * (P : ℤ) * r ≤ M * M * ((U : ℤ) + V + C - 2 * M) := by
    have hs : (U : ℤ) + V + C - 2 * M = (P : ℤ) - r - 1 := by omega
    rw [hs]
    have h1 : (0 : ℤ) ≤ (P : ℤ) - (2 * r + 3) := by omega
    have h0 : (0 : ℤ) ≤ (r : ℤ) := by positivity
    nlinarith [mul_nonneg h1 h0, mul_nonneg (mul_nonneg h0 h0) h0,
      mul_nonneg (mul_nonneg h0 h0) h1, mul_nonneg h0 h0]
  linarith

/-- The product bound. Integers at least 2, none above `P`, with sum `P + r` where `r ≤ P` and
`P ≥ 5`, multiply to at least `P * r`. (For `P = r = 3` it fails: 2 * 2 * 2 < 3 * 3, which is why
the entry excludes n = 6.) -/
theorem prod_ge_mul (L : List ℕ) (h2 : ∀ a ∈ L, 2 ≤ a) (P r : ℕ) (hS : L.sum = P + r)
    (hrP : r ≤ P) (hP : 5 ≤ P) (hmax : ∀ a ∈ L, a ≤ P) : P * r ≤ L.prod := by
  by_cases hbig : ∃ x ∈ L, r ≤ x
  · -- One part `x` with `r ≤ x ≤ P`: the product is at least `x * (P + r - x) ≥ P * r`.
    obtain ⟨x, hx, hrx⟩ := hbig
    have hperm := List.perm_cons_erase hx
    have hprod : L.prod = x * (L.erase x).prod := by rw [hperm.prod_eq, List.prod_cons]
    have hsum : L.sum = x + (L.erase x).sum := by rw [hperm.sum_eq, List.sum_cons]
    have hle := sum_le_prod (L.erase x) (fun a ha => h2 a (List.mem_of_mem_erase ha))
    have hxP := hmax x hx
    rw [hprod]
    calc P * r ≤ x * (L.erase x).sum := by nlinarith
      _ ≤ x * (L.erase x).prod := Nat.mul_le_mul_left _ hle
  · push Not at hbig
    rcases Nat.eq_zero_or_pos r with hr0 | hr
    · simp [hr0]
    obtain ⟨L1, z, L2, rfl, h1, h1'⟩ := split L r hr (by omega)
    have hz : z < r := hbig z (by simp)
    have hz2 : 2 ≤ z := h2 z (by simp)
    simp only [List.sum_append, List.sum_cons] at hS
    have hA := sum_le_prod L1 (fun a ha => h2 a (by simp [ha]))
    have hC := sum_le_prod L2 (fun a ha => h2 a (by simp [ha]))
    have hAz := sum_le_prod (z :: L1) (fun a ha => h2 a (by
      simp only [List.mem_cons] at ha; rcases ha with rfl | ha <;> simp [*]))
    simp only [List.sum_cons, List.prod_cons] at hAz
    rw [List.prod_append, List.prod_cons]
    by_cases hg : L1.sum + z ≤ P
    · -- Two groups, with sums `g = L1.sum + z` and `P + r - g`, both between `r` and `P`.
      calc P * r ≤ (z + L1.sum) * L2.sum := by nlinarith
        _ ≤ (z * L1.prod) * L2.prod := Nat.mul_le_mul hAz hC
        _ = L1.prod * (z * L2.prod) := by ring
    · -- Three groups, each of sum at most `M = r - 1`.
      have hr4 : 4 ≤ r := by omega
      calc P * r ≤ L1.sum * z * L2.sum := three_groups _ _ _ _ _ h1 hz (by omega) (by omega) hrP hP
        _ ≤ L1.prod * z * L2.prod := Nat.mul_le_mul (Nat.mul_le_mul_right _ hA) hC
        _ = L1.prod * (z * L2.prod) := by ring

/-! ### The sequence -/

theorem two_le_of_mem {m x : ℕ} (hx : x ∈ m.primeFactorsList) : 2 ≤ x :=
  (Nat.prime_of_mem_primeFactorsList hx).two_le

/-- A number whose prime factors add up to at least 2 is not 0. -/
theorem ne_zero_of_sopfr {m : ℕ} (h : 2 ≤ sopfr m) : m ≠ 0 := by
  rintro rfl; simp [sopfr_zero] at h

/-- The prime factors of `q * a (n - q)` add up to `n`, so `a n` is at most that. -/
theorem le_mul (a : ℕ → ℕ) (ha : ∀ n, 2 ≤ n → sopfr (a n) = n)
    (hmin : ∀ n m, 2 ≤ n → sopfr m = n → a n ≤ m) {n q : ℕ} (hq : q.Prime) (hqn : q < n - 1) :
    a n ≤ q * a (n - q) := by
  have h2 : 2 ≤ n - q := by omega
  apply hmin n _ (by omega)
  rw [sopfr_mul hq.ne_zero (ne_zero_of_sopfr (by rw [ha _ h2]; exact h2)), sopfr_prime hq, ha _ h2]
  omega

/-- Every prime factor `q` of `a n` (n composite) gives `a n = q * a (n - q)` with `q < n - 1`. -/
theorem eq_mul_of_mem (a : ℕ → ℕ) (ha : ∀ n, 2 ≤ n → sopfr (a n) = n)
    (hmin : ∀ n m, 2 ≤ n → sopfr m = n → a n ≤ m) {n q : ℕ} (hn : 2 ≤ n) (hc : ¬ n.Prime)
    (hq : q ∈ (a n).primeFactorsList) : q < n - 1 ∧ a n = q * a (n - q) := by
  have hm0 : a n ≠ 0 := ne_zero_of_sopfr (by rw [ha n hn]; exact hn)
  have hqp := Nat.prime_of_mem_primeFactorsList hq
  obtain ⟨k, hk⟩ := Nat.dvd_of_mem_primeFactorsList hq
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hm0 hk
  have hsum : sopfr k = n - q := by
    have := ha n hn; rw [hk, sopfr_mul hqp.ne_zero hk0, sopfr_prime hqp] at this; omega
  have hk1 : k ≠ 1 := by
    rintro rfl; have := ha n hn; rw [hk, mul_one, sopfr_prime hqp] at this; subst this; exact hc hqp
  have hk2 : 2 ≤ sopfr k := by
    obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd hk1
    have hpm : p ∈ k.primeFactorsList := (Nat.mem_primeFactorsList hk0).2 hp
    have := List.single_le_sum (fun _ _ => Nat.zero_le _) _ hpm
    unfold sopfr; have := hp.1.two_le; omega
  have hlt : q < n - 1 := by omega
  refine ⟨hlt, le_antisymm (le_mul a ha hmin hqp hlt) ?_⟩
  rw [hk]
  exact Nat.mul_le_mul_left _ (hmin _ _ (by omega) hsum)

theorem sopfr_two_pow (k : ℕ) : sopfr (2 ^ k) = 2 * k := by
  induction k with
  | zero => simp [sopfr_one]
  | succ k ih =>
    rw [pow_succ, sopfr_mul (by positivity) (by norm_num), ih, sopfr_prime Nat.prime_two]; ring

/-- The conjecture. The second part says the minimum over `P_n ≤ q < n - 1` is `a n`, and the
first says every `q` in that range gives at least `a n`. -/
theorem sycamore_marcus (a : ℕ → ℕ)
    (ha : ∀ n, 2 ≤ n → sopfr (a n) = n)
    (hmin : ∀ n m, 2 ≤ n → sopfr m = n → a n ≤ m)
    (n : ℕ) (hn : 4 ≤ n) (hc : ¬ n.Prime) (h6 : n ≠ 6) (P : ℕ)
    (hPn : IsGreatest {p | p.Prime ∧ p < n - 1 ∧ (if Even n then n - p else n - 3 - p).Prime} P) :
    (∀ q, q.Prime → P ≤ q → q < n - 1 → a n ≤ q * a (n - q)) ∧
    ∃ q, q.Prime ∧ P ≤ q ∧ q < n - 1 ∧ a n = q * a (n - q) := by
  refine ⟨fun q hq _ hqn => le_mul a ha hmin hq hqn, ?_⟩
  set m := a n with hm
  set B := m.primeFactorsList with hB
  have hm0 : m ≠ 0 := ne_zero_of_sopfr (by rw [ha n (by omega)]; omega)
  have hBsum : B.sum = n := ha n (by omega)
  have hBprod : B.prod = m := Nat.prod_primeFactorsList hm0
  have hB2 : ∀ x ∈ B, 2 ≤ x := fun x hx => two_le_of_mem hx
  -- It is enough that some prime factor of `a n` is at least `P`.
  suffices hex : ∃ q ∈ B, P ≤ q by
    obtain ⟨q, hqB, hPq⟩ := hex
    obtain ⟨hlt, heq⟩ := eq_mul_of_mem a ha hmin (by omega) hc hqB
    exact ⟨q, Nat.prime_of_mem_primeFactorsList hqB, hPq, hlt, heq⟩
  by_contra hno
  push Not at hno
  obtain ⟨⟨hP, hPlt, hpart⟩, hgreat⟩ := hPn
  -- `a n` would be a product with the prime factor `P`.
  have hPnot : ¬ P ∣ m := fun hd => by
    have := hno P ((Nat.mem_primeFactorsList hm0).2 ⟨hP, hd⟩); omega
  have hBne : B ≠ [] := by rintro h; rw [h] at hBsum; simp at hBsum; omega
  obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil B hBne
  have hP3 : 3 ≤ P := by have := hno x0 hx0; have := hB2 x0 hx0; omega
  have hBP : ∀ x ∈ B, x ≤ P := fun x hx => (hno x hx).le
  by_cases he : Even n
  · simp only [he, ite_true] at hpart
    obtain ⟨r, hr⟩ : ∃ r, r = n - P := ⟨_, rfl⟩
    rw [← hr] at hpart
    have hrP : r ≤ P := hgreat ⟨hpart, by omega, by
      simp only [he, ite_true]; rwa [show n - r = P by omega]⟩
    have hP5 : 5 ≤ P := by
      rcases (show P = 3 ∨ P = 4 ∨ 5 ≤ P by omega) with h | h | h
      · obtain ⟨k, hk⟩ := he; have := hpart.two_le; omega
      · subst h; norm_num at hP
      · exact h
    have hlow := prod_ge_mul B hB2 P r (by omega) hrP hP5 hBP
    have hup : m ≤ P * r := hmin n _ (by omega) (by
      rw [sopfr_mul hP.ne_zero hpart.ne_zero, sopfr_prime hP, sopfr_prime hpart]; omega)
    exact hPnot ⟨r, by rw [hBprod] at hlow; omega⟩
  · simp only [he, ite_false] at hpart
    obtain ⟨r, hr⟩ : ∃ r, r = n - 3 - P := ⟨_, rfl⟩
    rw [← hr] at hpart
    have hodd : n % 2 = 1 := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 he)
    have hr2 := hpart.two_le
    have hrP : r ≤ P := hgreat ⟨hpart, by omega, by
      simp only [he, ite_false]; rwa [show n - 3 - r = P by omega]⟩
    have hPodd : P % 2 = 1 := by
      rcases hP.eq_two_or_odd with h | h
      · omega
      · exact h
    have hrodd : r % 2 = 1 := by omega
    have hup : m ≤ 3 * P * r := hmin n _ (by omega) (by
      rw [sopfr_mul (by positivity) hpart.ne_zero, sopfr_mul (by norm_num) hP.ne_zero,
        sopfr_prime Nat.prime_three, sopfr_prime hP, sopfr_prime hpart]; omega)
    suffices hlow : 3 * P * r ≤ m by
      exact hPnot ⟨3 * r, by rw [le_antisymm hup hlow]; ring⟩
    -- Odd and even prime factors.
    set O := B.filter (fun x => x % 2 = 1) with hO
    set E := B.filter (fun x => !decide (x % 2 = 1)) with hE
    have hperm : (O ++ E).Perm B := by
      exact List.filter_append_perm (fun x => decide (x % 2 = 1)) B
    have hE2 : E = List.replicate E.length 2 := by
      rw [List.eq_replicate_iff]; refine ⟨rfl, fun b hb => ?_⟩
      rw [hE, List.mem_filter] at hb
      obtain ⟨hbB, hbo⟩ := hb
      rcases (Nat.prime_of_mem_primeFactorsList hbB).eq_two_or_odd with h | h
      · exact h
      · simp at hbo; omega
    have hOmem : ∀ u ∈ O, u ∈ B ∧ u % 2 = 1 := fun u hu => by
      rw [hO, List.mem_filter] at hu; simpa using hu
    have hsumOE : O.sum + 2 * E.length = n := by
      rw [← hBsum, ← hperm.sum_eq, List.sum_append, hE2]; simp; ring
    have hprodOE : O.prod * 2 ^ E.length = m := by
      rw [← hBprod, ← hperm.prod_eq, List.prod_append, hE2]; simp
    by_cases hsmall : ∃ w ∈ B, w % 2 = 1 ∧ w ≤ r
    · -- An odd prime factor `w ≤ r`: the rest has sum `P + (r + 3 - w)`.
      obtain ⟨w, hwB, hwo, hwr⟩ := hsmall
      have hw3 : 3 ≤ w := by have := hB2 w hwB; omega
      have hP5 : 5 ≤ P := by
        have := hno w hwB
        rcases (show P = 4 ∨ 5 ≤ P by omega) with h | h
        · subst h; norm_num at hP
        · exact h
      have hpw := List.perm_cons_erase hwB
      have hprod : B.prod = w * (B.erase w).prod := by rw [hpw.prod_eq, List.prod_cons]
      have hsum : B.sum = w + (B.erase w).sum := by rw [hpw.sum_eq, List.sum_cons]
      have hlow := prod_ge_mul (B.erase w) (fun a ha => hB2 a (List.mem_of_mem_erase ha))
        P (r + 3 - w) (by omega) (by omega) hP5 (fun a ha => hBP a (List.mem_of_mem_erase ha))
      rw [← hBprod, hprod]
      have hkey : 3 * r ≤ w * (r + 3 - w) := by
        have : r + 3 - w + w = r + 3 := by omega
        nlinarith
      calc 3 * P * r = P * (3 * r) := by ring
        _ ≤ P * (w * (r + 3 - w)) := Nat.mul_le_mul_left _ hkey
        _ = w * (P * (r + 3 - w)) := by ring
        _ ≤ w * (B.erase w).prod := Nat.mul_le_mul_left _ hlow
    · push Not at hsmall
      match hOc : O with
      | [] => simp at hsumOE; omega
      | [u] =>
        -- One odd prime factor and at least four 2s: swapping 2, 2, 2, 2 for 3, 5 is cheaper.
        exfalso
        have hu := hOmem u (by simp)
        have hk4 : 4 ≤ E.length := by
          simp at hsumOE; have := hno u hu.1; omega
        simp at hprodOE
        set m0 := u * 2 ^ (E.length - 4)
        have hu0 : u ≠ 0 := by have := hB2 u hu.1; omega
        have hm0' : m0 ≠ 0 := by positivity
        have hmeq : m = m0 * 16 := by
          rw [← hprodOE]
          simp only [m0]
          rw [show E.length = E.length - 4 + 4 by omega, pow_add]
          simp; ring
        have h16 : sopfr 16 = 8 := by
          rw [show (16 : ℕ) = 2 ^ 4 by norm_num, sopfr_two_pow]
        have h15 : sopfr 15 = 8 := by
          rw [show (15 : ℕ) = 3 * 5 by norm_num, sopfr_mul (by norm_num) (by norm_num),
            sopfr_prime Nat.prime_three, sopfr_prime (by norm_num)]
        have hle := hmin n (m0 * 15) (by omega) (by
          rw [sopfr_mul hm0' (by norm_num), h15, ← h16, ← sopfr_mul hm0' (by norm_num), ← hmeq,
            hm, ha n (by omega)])
        have : 0 < m0 := Nat.pos_of_ne_zero hm0'
        omega
      | [u1, u2] =>
        have h1 := (hOmem u1 (by simp)).2
        have h2 := (hOmem u2 (by simp)).2
        simp at hsumOE; omega
      | u1 :: u2 :: u3 :: rest =>
        -- Three odd prime factors, each at least `r + 2`.
        have hbig : ∀ u ∈ [u1, u2, u3], r + 2 ≤ u := by
          intro u hu
          have := hOmem u (by simp at hu ⊢; rcases hu with h | h | h <;> simp [h])
          have := hsmall u this.1 this.2; omega
        have hu1 := hbig u1 (by simp)
        have hu2 := hbig u2 (by simp)
        have hu3 := hbig u3 (by simp)
        set T := u3 :: rest ++ E with hT
        have hT2 : ∀ x ∈ T, 2 ≤ x := by
          intro x hx
          rw [hT, List.mem_append] at hx
          rcases hx with hx | hx
          · exact hB2 x (hOmem x (by simp at hx ⊢; tauto)).1
          · rw [hE, List.mem_filter] at hx; exact hB2 x hx.1
        have hTs := sum_le_prod T hT2
        have hsT : u1 + u2 + T.sum = n := by
          rw [← hBsum, ← hperm.sum_eq, hT]; simp; ring
        have hpT : u1 * u2 * T.prod = m := by
          rw [← hBprod, ← hperm.prod_eq, hT]; simp; ring
        have hu3T : u3 ≤ T.sum := by rw [hT]; simp only [List.sum_append, List.sum_cons]; omega
        rw [← hpT]
        calc 3 * P * r ≤ u1 * u2 * T.sum := three_large _ _ _ _ _ hu1 hu2 (by omega) (by omega)
          _ ≤ u1 * u2 * T.prod := Nat.mul_le_mul_left _ hTs

/-! ### A concrete `a`, so the hypotheses are not contradictory -/

theorem exists_sopfr (n : ℕ) (hn : 2 ≤ n) : ∃ m, sopfr m = n := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨2 ^ k, by rw [sopfr_two_pow]; omega⟩
  · refine ⟨3 * 2 ^ (k - 1), ?_⟩
    rw [sopfr_mul (by norm_num) (by positivity), sopfr_prime Nat.prime_three, sopfr_two_pow]
    omega

open Classical in
/-- The smallest number whose prime factors add up to `n` (0 when there is none). -/
noncomputable def a0 (n : ℕ) : ℕ := if h : ∃ m, sopfr m = n then Nat.find h else 0

theorem a0_spec (n : ℕ) (hn : 2 ≤ n) : sopfr (a0 n) = n := by
  have h := exists_sopfr n hn
  classical
  simp only [a0, h, dite_true]
  exact Nat.find_spec h

theorem a0_min (n m : ℕ) (hn : 2 ≤ n) (hm : sopfr m = n) : a0 n ≤ m := by
  have h := exists_sopfr n hn
  classical
  simp only [a0, h, dite_true]
  exact Nat.find_min' h hm

/-- The theorem applies to the sequence itself. -/
theorem sycamore_marcus_a0 (n : ℕ) (hn : 4 ≤ n) (hc : ¬ n.Prime) (h6 : n ≠ 6) (P : ℕ)
    (hPn : IsGreatest {p | p.Prime ∧ p < n - 1 ∧ (if Even n then n - p else n - 3 - p).Prime} P) :
    ∃ q, q.Prime ∧ P ≤ q ∧ q < n - 1 ∧ a0 n = q * a0 (n - q) :=
  (sycamore_marcus a0 a0_spec a0_min n hn hc h6 P hPn).2

end A056240
