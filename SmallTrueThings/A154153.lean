/-
The family {k : c + k(k+1)/2 is a square}, for every c ≥ 1 (A175032 lists it: A006451,
A154138 to A154154, ...), and Mathar's conjectures on the eight members still marked as such:
A154141 (c = 8), A154143 (10), A154144 (13), A154148 (21), A154150 (24), A154151 (25),
A154153 (28), A154154 (30).

Each of those entries (R. J. Mathar, Oct 18 2009) carries, marked as conjectures,
  a(n) = a(n-1) + 6a(n-2) - 6a(n-3) - a(n-4) + a(n-5)
and a rational generating function with denominator (x-1)(x^2-2x-1)(x^2+2x-1).

The general theorem, `A154153.chains`. With x = 2k+1 and N = 8c - 1 the condition reads
x^2 + N = 8y^2. Call k small when x^2 < 8N. If a lists the set in increasing order and m is
the number of small members, then a(n+m) = T(a(n)) for every n, where T(k) = 3k + 1 + 4y is
the unit 3 + √8 acting on (x, y). Hence a(n+2m) = 6a(n+m) - a(n) + 2 (`A154153.six`).

Why: T maps members to members, strictly increasing, and never to a small one; and every
member that is not small is T of a smaller member (the descent (x, y) ↦ (3x - 8y, 3y - x)).
So the members past the first m are exactly the T-images, in the same order.

No condition on how the chains interleave is needed: it holds for every c. For the eight
entries m = 2, which gives Mathar's recurrence and generating functions.
-/
import Mathlib

open PowerSeries

namespace A154153

/-- c plus the k-th triangular number is a square. -/
def S (c k : ℕ) : Prop := ∃ m, c + k * (k + 1) / 2 = m ^ 2

/-- (2k+1)^2 < 8N, N = 8c - 1: the members that are not images of the step. -/
def small (c k : ℕ) : Prop := (2 * k + 1) ^ 2 < 8 * (8 * c - 1)

/-- The square root of c + k(k+1)/2. -/
def yy (c k : ℕ) : ℕ := Nat.sqrt (c + k * (k + 1) / 2)

/-- The unit 3 + √8 acting on k: (x, y) ↦ (3x + 8y, x + 3y) with x = 2k + 1. -/
def T (c k : ℕ) : ℕ := 3 * k + 1 + 4 * yy c k

lemma tri_iff {c : ℕ} (hc : 1 ≤ c) (k y : ℕ) :
    c + k * (k + 1) / 2 = y ^ 2 ↔ (2 * k + 1) ^ 2 + (8 * c - 1) = 8 * y ^ 2 := by
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
  have hsq : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
  rw [hsq, hj]
  omega

lemma yy_eq {c k m : ℕ} (h : c + k * (k + 1) / 2 = m ^ 2) : yy c k = m := by
  simp only [yy, h, Nat.sqrt_eq']

lemma pell {c k : ℕ} (hc : 1 ≤ c) (h : S c k) :
    (2 * k + 1) ^ 2 + (8 * c - 1) = 8 * yy c k ^ 2 := by
  obtain ⟨m, hm⟩ := h
  rw [yy_eq hm]
  exact (tri_iff hc k m).1 hm

lemma T_spec {c k : ℕ} (hc : 1 ≤ c) (h : S c k) :
    S c (T c k) ∧ yy c (T c k) = (2 * k + 1) + 3 * yy c k := by
  have hp := pell hc h
  obtain ⟨N, hN⟩ : ∃ N, N = 8 * c - 1 := ⟨_, rfl⟩
  have key : c + T c k * (T c k + 1) / 2 = ((2 * k + 1) + 3 * yy c k) ^ 2 := by
    rw [tri_iff hc]
    have e : 2 * T c k + 1 = 3 * (2 * k + 1) + 8 * yy c k := by simp only [T]; ring
    rw [e, ← hN]
    rw [← hN] at hp
    nlinarith [hp]
  exact ⟨⟨_, key⟩, yy_eq key⟩

lemma T_mono {c k k' : ℕ} (hc : 1 ≤ c) (hk : S c k) (hk' : S c k') (hlt : k < k') :
    T c k < T c k' := by
  have h1 := pell hc hk
  have h2 := pell hc hk'
  have hy : yy c k ≤ yy c k' := by
    by_contra hcon
    push Not at hcon
    have e1 : yy c k' ^ 2 < yy c k ^ 2 := Nat.pow_lt_pow_left hcon two_ne_zero
    have e2 : (2 * k + 1) ^ 2 < (2 * k' + 1) ^ 2 :=
      Nat.pow_lt_pow_left (by omega) two_ne_zero
    omega
  simp only [T]
  omega

lemma T_not_small {c k : ℕ} (hc : 1 ≤ c) (hk : S c k) : ¬ small c (T c k) := by
  have hp := pell hc hk
  simp only [small, not_lt]
  have e : 2 * T c k + 1 = 3 * (2 * k + 1) + 8 * yy c k := by simp only [T]; ring
  rw [e]
  obtain ⟨N, hN⟩ : ∃ N, N = 8 * c - 1 := ⟨_, rfl⟩
  rw [← hN] at hp ⊢
  nlinarith [hp]

/-- The descent: a member that is not small is T of a member. -/
lemma descent {c k : ℕ} (hc : 1 ≤ c) (hk : S c k) (hs : ¬ small c k) :
    ∃ k', S c k' ∧ T c k' = k := by
  have hp := pell hc hk
  simp only [small, not_lt] at hs
  obtain ⟨N, hN⟩ : ∃ N, N = 8 * c - 1 := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = 2 * k + 1 := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = yy c k := ⟨_, rfl⟩
  rw [← hN, ← hx, ← hy] at hp
  rw [← hN, ← hx] at hs
  have hN7 : 7 ≤ N := by omega
  have h1 : 8 * y ≤ 3 * x := by
    by_contra h; push Not at h; nlinarith
  have h2 : x ≤ 3 * y := by
    by_contra h; push Not at h; nlinarith
  obtain ⟨x', hx'⟩ : ∃ x', x' = 3 * x - 8 * y := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y', y' = 3 * y - x := ⟨_, rfl⟩
  have ex : x = 3 * x' + 8 * y' := by omega
  have ey : y = x' + 3 * y' := by omega
  have hodd : x' % 2 = 1 := by omega
  have h' : x' ^ 2 + N = 8 * y' ^ 2 := by
    rw [ex, ey] at hp; nlinarith [hp]
  have hk'x : 2 * ((x' - 1) / 2) + 1 = x' := by omega
  have hS' : c + (x' - 1) / 2 * ((x' - 1) / 2 + 1) / 2 = y' ^ 2 := by
    rw [tri_iff hc, hk'x, ← hN]; exact h'
  refine ⟨(x' - 1) / 2, ⟨y', hS'⟩, ?_⟩
  simp only [T, yy_eq hS']
  omega

lemma T_gt (c k : ℕ) : k < T c k := by simp only [T]; omega

lemma TT {c k : ℕ} (hc : 1 ≤ c) (hk : S c k) :
    T c (T c k) = 17 * k + 8 + 24 * yy c k := by
  rw [show T c (T c k) = 3 * T c k + 1 + 4 * yy c (T c k) from rfl, (T_spec hc hk).2]
  simp only [T]
  ring

/-- **The family theorem.** If `a` lists {k : c + k(k+1)/2 is a square} in increasing order
from index 0, and the first m members are exactly the small ones, then a(n+m) = T(a(n)). -/
theorem chains {c : ℕ} (hc : 1 ≤ c) (a : ℕ → ℕ) (ha : StrictMono a)
    (hr : ∀ k, S c k ↔ ∃ n, a n = k) (m : ℕ) (hm : ∀ n, n < m ↔ small c (a n)) :
    ∀ n, a (n + m) = T c (a n) := by
  have hS : ∀ n, S c (a n) := fun n => (hr _).2 ⟨n, rfl⟩
  have hg : StrictMono (fun n => T c (a n)) :=
    fun i j hij => T_mono hc (hS i) (hS j) (ha hij)
  have hh : StrictMono (fun n => a (n + m)) := fun i j hij => ha (by omega)
  have hrange : Set.range (fun n => a (n + m)) = Set.range (fun n => T c (a n)) := by
    ext k
    simp only [Set.mem_range]
    constructor
    · rintro ⟨n, rfl⟩
      have hs : ¬ small c (a (n + m)) := fun h => by have := (hm _).2 h; omega
      obtain ⟨k', hk', hT⟩ := descent hc (hS _) hs
      obtain ⟨i, rfl⟩ := (hr _).1 hk'
      exact ⟨i, hT⟩
    · rintro ⟨n, rfl⟩
      obtain ⟨j, hj⟩ := (hr _).1 (T_spec hc (hS n)).1
      have hjm : m ≤ j := by
        by_contra h
        push Not at h
        have := (hm j).1 h
        rw [hj] at this
        exact T_not_small hc (hS n) this
      exact ⟨j - m, by rw [Nat.sub_add_cancel hjm]; exact hj⟩
  intro n
  exact congrFun ((hh.range_inj_of_wellFoundedLT hg).1 hrange) n

/-- Two steps of the unit: a(n+2m) = 6a(n+m) - a(n) + 2. -/
theorem six {c : ℕ} (hc : 1 ≤ c) (a : ℕ → ℕ) (ha : StrictMono a)
    (hr : ∀ k, S c k ↔ ∃ n, a n = k) (m : ℕ) (hm : ∀ n, n < m ↔ small c (a n)) (n : ℕ) :
    (a (n + 2 * m) : ℤ) = 6 * a (n + m) - a n + 2 := by
  have h := chains hc a ha hr m hm
  have hS : S c (a n) := (hr _).2 ⟨n, rfl⟩
  have e2 := h (n + m)
  rw [show n + m + m = n + 2 * m by ring, h n, TT hc hS] at e2
  rw [e2, h n]
  simp only [T]
  push_cast
  ring

/-- The set is infinite once it has a member, so it can be listed. -/
lemma S_infinite {c k0 : ℕ} (hc : 1 ≤ c) (h0 : S c k0) : (Set.ofPred (S c)).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  induction B with
  | zero => exact ⟨T c k0, (T_spec hc h0).1, by have := T_gt c k0; omega⟩
  | succ B ih =>
    obtain ⟨k, hk, hB⟩ := ih
    exact ⟨T c k, (T_spec hc hk).1, by have := T_gt c k; omega⟩

lemma small_mono {c k k' : ℕ} (hkk : k ≤ k') (h : small c k') : small c k := by
  simp only [small] at *
  have : (2 * k + 1) ^ 2 ≤ (2 * k' + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

/-- When exactly two members are small, they are a(0) and a(1), so m = 2. -/
lemma first_two {c : ℕ} (a : ℕ → ℕ) (ha : StrictMono a) (hr : ∀ k, S c k ↔ ∃ n, a n = k)
    {k1 k2 : ℕ} (h1 : S c k1) (h2 : S c k2) (h12 : k1 < k2) (hs2 : small c k2)
    (honly : ∀ k, S c k → small c k → k = k1 ∨ k = k2) :
    a 0 = k1 ∧ a 1 = k2 ∧ ∀ n, n < 2 ↔ small c (a n) := by
  have hS : ∀ n, S c (a n) := fun n => (hr _).2 ⟨n, rfl⟩
  obtain ⟨j1, hj1⟩ := (hr k1).1 h1
  obtain ⟨j2, hj2⟩ := (hr k2).1 h2
  have a0le : a 0 ≤ k1 := hj1 ▸ ha.monotone (Nat.zero_le j1)
  have a0 : a 0 = k1 := by
    rcases honly _ (hS 0) (small_mono (by omega) hs2) with h | h <;> omega
  have hj2' : 1 ≤ j2 := by
    by_contra h
    have : j2 = 0 := by omega
    subst this; omega
  have a1le : a 1 ≤ k2 := hj2 ▸ ha.monotone hj2'
  have a01 : a 0 < a 1 := ha (by norm_num)
  have a1 : a 1 = k2 := by
    rcases honly _ (hS 1) (small_mono a1le hs2) with h | h <;> omega
  refine ⟨a0, a1, fun n => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  · interval_cases n
    · rw [a0]; exact small_mono h12.le hs2
    · rw [a1]; exact hs2
  · by_contra hc
    have : a 1 < a n := ha (by omega)
    rcases honly _ (hS n) hn with h | h <;> omega

/-- The two-chain case, indexed from 1 as on the entries. -/
theorem two_chain {c : ℕ} (hc : 1 ≤ c) {k1 k2 : ℕ} (h1 : S c k1) (h2 : S c k2) (h12 : k1 < k2)
    (hs2 : small c k2) (honly : ∀ k, S c k → small c k → k = k1 ∨ k = k2)
    (a : ℕ → ℕ) (hmono : ∀ n, 1 ≤ n → a n < a (n + 1))
    (hset : ∀ k, S c k ↔ ∃ n, 1 ≤ n ∧ a n = k) :
    a 1 = k1 ∧ a 2 = k2 ∧ a 3 = T c k1 ∧ a 4 = T c k2 ∧
    (∀ n, 5 ≤ n → (a n : ℤ) = 6 * a (n - 2) - a (n - 4) + 2) ∧
    (∀ n, 6 ≤ n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5)) := by
  have hb : StrictMono (fun n => a (n + 1)) :=
    strictMono_nat_of_lt_succ (fun n => hmono (n + 1) (by omega))
  have hr : ∀ k, S c k ↔ ∃ n, a (n + 1) = k := by
    intro k
    rw [hset]
    constructor
    · rintro ⟨n, hn, h⟩; exact ⟨n - 1, by rw [Nat.sub_add_cancel hn]; exact h⟩
    · rintro ⟨n, h⟩; exact ⟨n + 1, by omega, h⟩
  obtain ⟨b0, b1, hm⟩ := first_two (fun n => a (n + 1)) hb hr h1 h2 h12 hs2 honly
  have hch := chains hc (fun n => a (n + 1)) hb hr 2 hm
  have hsix := six hc (fun n => a (n + 1)) hb hr 2 hm
  have a3 : a 3 = T c k1 := by rw [← b0]; exact hch 0
  have a4 : a 4 = T c k2 := by rw [← b1]; exact hch 1
  have four : ∀ n, 5 ≤ n → (a n : ℤ) = 6 * a (n - 2) - a (n - 4) + 2 := by
    intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 5 := ⟨n - 5, by omega⟩
    have := hsix j
    rw [show j + 2 * 2 + 1 = j + 5 by ring, show j + 2 + 1 = j + 5 - 2 by omega,
      show j + 1 = j + 5 - 4 by omega] at this
    exact this
  refine ⟨b0, b1, a3, a4, four, fun n hn => ?_⟩
  have e1 := four n (by omega)
  have e2 := four (n - 1) (by omega)
  rw [show n - 1 - 2 = n - 3 by omega, show n - 1 - 4 = n - 5 by omega] at e2
  linarith

/-- The common denominator of the eight generating functions. -/
noncomputable def den : ℤ⟦X⟧ := (X - 1) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)

/-- Mathar's recurrence is the statement den · A = (a polynomial of degree 5). -/
lemma gf (a : ℕ → ℕ) (hrec : ∀ n, 6 ≤ n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5))
    (e1 e2 e3 e4 e5 : ℤ) (h1 : e1 = -(a 1 : ℤ)) (h2 : e2 = (a 1 : ℤ) - a 2)
    (h3 : e3 = -(a 3 : ℤ) + a 2 + 6 * a 1) (h4 : e4 = -(a 4 : ℤ) + a 3 + 6 * a 2 - 6 * a 1)
    (h5 : e5 = -(a 5 : ℤ) + a 4 + 6 * a 3 - 6 * a 2 - a 1) :
    den * mk (fun n => if n = 0 then (0 : ℤ) else a n) =
      C e1 * X ^ 1 + C e2 * X ^ 2 + C e3 * X ^ 3 + C e4 * X ^ 4 + C e5 * X ^ 5 := by
  set A := mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have hexp : den * A = - A + X ^ 1 * A + C (6 : ℤ) * (X ^ 2 * A) - C (6 : ℤ) * (X ^ 3 * A)
      - X ^ 4 * A + X ^ 5 * A := by
    simp only [den, map_ofNat]; ring
  rw [hexp]
  ext n
  have cX : ∀ d : ℕ, coeff n (X ^ d : ℤ⟦X⟧) = if n = d then 1 else 0 :=
    fun d => coeff_X_pow n d
  simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_X_pow_mul', hA, coeff_mk, cX]
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> simp [h1, h2, h3, h4, h5]; ring
  · have := hrec n hn
    simp only [show ¬ n = 0 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega,
      show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega,
      show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
      show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
      ite_true, ite_false]
    linarith

/-- A concrete listing: the members in increasing order, indexed from 1. -/
noncomputable def listing (c n : ℕ) : ℕ := Nat.nth (S c) (n - 1)

theorem listing_spec {c k0 : ℕ} (hc : 1 ≤ c) (h0 : S c k0) :
    (∀ n, 1 ≤ n → listing c n < listing c (n + 1)) ∧
    (∀ k, S c k ↔ ∃ n, 1 ≤ n ∧ listing c n = k) := by
  have hinf := S_infinite hc h0
  refine ⟨fun n hn => ?_, fun k => ?_⟩
  · simp only [listing, show n + 1 - 1 = (n - 1) + 1 by omega]
    exact Nat.nth_strictMono hinf (Nat.lt_succ_self _)
  · have := congrArg (k ∈ ·) (Nat.range_nth_of_infinite hinf)
    simp only [Set.mem_range, eq_iff_iff] at this
    change (∃ y, Nat.nth (S c) y = k) ↔ S c k at this
    rw [← this]
    constructor
    · rintro ⟨n, rfl⟩; exact ⟨n + 1, by omega, rfl⟩
    · rintro ⟨n, -, rfl⟩; exact ⟨n - 1, rfl⟩

/-- Only k1 and k2 are small members: a finite search over k and y. -/
macro "only_two" kb:num yb:num : tactic => `(tactic| (
  intro k hk hs
  obtain ⟨y, hy⟩ := hk
  rw [tri_iff (by norm_num)] at hy
  simp only [small] at hs
  norm_num at hy hs
  have hk' : k ≤ $kb := by nlinarith
  have hy' : y ≤ $yb := by nlinarith
  interval_cases k <;> interval_cases y <;> simp_all))

/-- From `two_chain` and `gf` to an entry's printed formulas. -/
macro "entry" a:ident hmono:ident hset:ident c:num k1:num y1:num k2:num y2:num kb:num yb:num : tactic => `(tactic| (
  obtain ⟨i1, i2, i3, i4, five, rec⟩ := two_chain (c := $c) (by norm_num)
    (k1 := $k1) (k2 := $k2) ⟨$y1, by norm_num⟩ ⟨$y2, by norm_num⟩ (by norm_num)
    (by norm_num [small]) (by only_two $kb $yb) $a $hmono $hset
  rw [show T $c $k1 = 3 * $k1 + 1 + 4 * $y1 from by
        simp only [T, yy_eq (show $c + $k1 * ($k1 + 1) / 2 = $y1 ^ 2 by norm_num)]] at i3
  rw [show T $c $k2 = 3 * $k2 + 1 + 4 * $y2 from by
        simp only [T, yy_eq (show $c + $k2 * ($k2 + 1) / 2 = $y2 ^ 2 by norm_num)]] at i4
  norm_num at i3 i4
  have i5 := five 5 le_rfl
  norm_num [i1, i3] at i5
  have i5' : $a 5 = 6 * $a 3 - $a 1 + 2 := by omega
  norm_num [i1, i3] at i5'
  refine ⟨⟨i1, i2, i3, i4, i5'⟩, rec, ?_, five⟩
  have g := gf $a rec _ _ _ _ _ rfl rfl rfl rfl rfl
  rw [i1, i2, i3, i4, i5'] at g
  have hden : den = (X - 1) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) := rfl
  first
    | (rw [show ((1 : ℤ⟦X⟧) - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) = -den by
          rw [hden]; ring, neg_mul, g]
       try simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
       norm_num
       try simp only [map_neg, map_ofNat, map_one, map_zero]
       ring)
    | (rw [show ((X : ℤ⟦X⟧) - 1) * (X ^ 2 + 2 * X - 1) * (X ^ 2 - 2 * X - 1) = den by
          rw [hden]; ring, g]
       try simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
       norm_num
       try simp only [map_neg, map_ofNat, map_one, map_zero]
       ring)
    | (rw [show ((X : ℤ⟦X⟧) - 1) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) = den by
          rw [hden], g]
       try simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
       norm_num
       try simp only [map_neg, map_ofNat, map_one, map_zero]
       ring)))

/-- **A154141** (c = 8): Mathar's recurrence and generating function, as printed on the entry,
for any `a` listing {k : 8 + k(k+1)/2 is a square} in increasing order from index 1. -/
theorem a154141 (a : ℕ → ℕ) (hmono : ∀ n, 1 ≤ n → a n < a (n + 1))
    (hset : ∀ k, (∃ m, 8 + k * (k + 1) / 2 = m ^ 2) ↔ ∃ n, 1 ≤ n ∧ a n = k) :
    (a 1 = 1 ∧ a 2 = 7 ∧ a 3 = 16 ∧ a 4 = 46 ∧ a 5 = 97) ∧
    (∀ n, 6 ≤ n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    (1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) *
        mk (fun n => if n = 0 then (0 : ℤ) else a n) =
      X * (1 + 6 * X + 3 * X ^ 2 - 6 * X ^ 3 - 2 * X ^ 4) ∧
    (∀ n, 5 ≤ n → (a n : ℤ) = 6 * a (n - 2) - a (n - 4) + 2) := by
  entry a hmono hset 8 1 3 7 6 10 8

/-- **A154143** (c = 10): Mathar's recurrence and generating function, as printed on the entry,
for any `a` listing {k : 10 + k(k+1)/2 is a square} in increasing order from index 1. -/
theorem a154143 (a : ℕ → ℕ) (hmono : ∀ n, 1 ≤ n → a n < a (n + 1))
    (hset : ∀ k, (∃ m, 10 + k * (k + 1) / 2 = m ^ 2) ↔ ∃ n, 1 ≤ n ∧ a n = k) :
    (a 1 = 3 ∧ a 2 = 5 ∧ a 3 = 26 ∧ a 4 = 36 ∧ a 5 = 155) ∧
    (∀ n, 6 ≤ n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    (1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) *
        mk (fun n => if n = 0 then (0 : ℤ) else a n) =
      X * (3 + 2 * X + 3 * X ^ 2 - 2 * X ^ 3 - 4 * X ^ 4) ∧
    (∀ n, 5 ≤ n → (a n : ℤ) = 6 * a (n - 2) - a (n - 4) + 2) := by
  entry a hmono hset 10 3 4 5 5 12 9

/-- **A154144** (c = 13): Mathar's recurrence and generating function, as printed on the entry,
for any `a` listing {k : 13 + k(k+1)/2 is a square} in increasing order from index 1. -/
theorem a154144 (a : ℕ → ℕ) (hmono : ∀ n, 1 ≤ n → a n < a (n + 1))
    (hset : ∀ k, (∃ m, 13 + k * (k + 1) / 2 = m ^ 2) ↔ ∃ n, 1 ≤ n ∧ a n = k) :
    (a 1 = 2 ∧ a 2 = 8 ∧ a 3 = 23 ∧ a 4 = 53 ∧ a 5 = 138) ∧
    (∀ n, 6 ≤ n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    (1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) *
        mk (fun n => if n = 0 then (0 : ℤ) else a n) =
      X * (2 + 6 * X + 3 * X ^ 2 - 6 * X ^ 3 - 3 * X ^ 4) ∧
    (∀ n, 5 ≤ n → (a n : ℤ) = 6 * a (n - 2) - a (n - 4) + 2) := by
  entry a hmono hset 13 2 4 8 7 13 10

/-- **A154148** (c = 21): Mathar's recurrence and generating function, as printed on the entry,
for any `a` listing {k : 21 + k(k+1)/2 is a square} in increasing order from index 1. -/
theorem a154148 (a : ℕ → ℕ) (hmono : ∀ n, 1 ≤ n → a n < a (n + 1))
    (hset : ∀ k, (∃ m, 21 + k * (k + 1) / 2 = m ^ 2) ↔ ∃ n, 1 ≤ n ∧ a n = k) :
    (a 1 = 5 ∧ a 2 = 7 ∧ a 3 = 40 ∧ a 4 = 50 ∧ a 5 = 237) ∧
    (∀ n, 6 ≤ n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    (X - 1) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) *
        mk (fun n => if n = 0 then (0 : ℤ) else a n) =
      X * (-5 - 2 * X - 3 * X ^ 2 + 2 * X ^ 3 + 6 * X ^ 4) ∧
    (∀ n, 5 ≤ n → (a n : ℤ) = 6 * a (n - 2) - a (n - 4) + 2) := by
  entry a hmono hset 21 5 6 7 7 17 13

/-- **A154150** (c = 24): Mathar's recurrence and generating function, as printed on the entry,
for any `a` listing {k : 24 + k(k+1)/2 is a square} in increasing order from index 1. -/
theorem a154150 (a : ℕ → ℕ) (hmono : ∀ n, 1 ≤ n → a n < a (n + 1))
    (hset : ∀ k, (∃ m, 24 + k * (k + 1) / 2 = m ^ 2) ↔ ∃ n, 1 ≤ n ∧ a n = k) :
    (a 1 = 1 ∧ a 2 = 15 ∧ a 3 = 24 ∧ a 4 = 94 ∧ a 5 = 145) ∧
    (∀ n, 6 ≤ n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    (X - 1) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) *
        mk (fun n => if n = 0 then (0 : ℤ) else a n) =
      X * (-1 - 14 * X - 3 * X ^ 2 + 14 * X ^ 3 + 2 * X ^ 4) ∧
    (∀ n, 5 ≤ n → (a n : ℤ) = 6 * a (n - 2) - a (n - 4) + 2) := by
  entry a hmono hset 24 1 5 15 12 19 14

/-- **A154151** (c = 25): Mathar's recurrence and generating function, as printed on the entry,
for any `a` listing {k : 25 + k(k+1)/2 is a square} in increasing order from index 1. -/
theorem a154151 (a : ℕ → ℕ) (hmono : ∀ n, 1 ≤ n → a n < a (n + 1))
    (hset : ∀ k, (∃ m, 25 + k * (k + 1) / 2 = m ^ 2) ↔ ∃ n, 1 ≤ n ∧ a n = k) :
    (a 1 = 0 ∧ a 2 = 18 ∧ a 3 = 21 ∧ a 4 = 111 ∧ a 5 = 128) ∧
    (∀ n, 6 ≤ n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    (X - 1) * (X ^ 2 + 2 * X - 1) * (X ^ 2 - 2 * X - 1) *
        mk (fun n => if n = 0 then (0 : ℤ) else a n) =
      X ^ 2 * (-18 - 3 * X + 18 * X ^ 2 + X ^ 3) ∧
    (∀ n, 5 ≤ n → (a n : ℤ) = 6 * a (n - 2) - a (n - 4) + 2) := by
  entry a hmono hset 25 0 5 18 14 19 14

/-- **A154153** (c = 28): Mathar's recurrence and generating function, as printed on the entry,
for any `a` listing {k : 28 + k(k+1)/2 is a square} in increasing order from index 1. -/
theorem a154153 (a : ℕ → ℕ) (hmono : ∀ n, 1 ≤ n → a n < a (n + 1))
    (hset : ∀ k, (∃ m, 28 + k * (k + 1) / 2 = m ^ 2) ↔ ∃ n, 1 ≤ n ∧ a n = k) :
    (a 1 = 6 ∧ a 2 = 8 ∧ a 3 = 47 ∧ a 4 = 57 ∧ a 5 = 278) ∧
    (∀ n, 6 ≤ n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    (X - 1) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) *
        mk (fun n => if n = 0 then (0 : ℤ) else a n) =
      X * (-6 - 2 * X - 3 * X ^ 2 + 2 * X ^ 3 + 7 * X ^ 4) ∧
    (∀ n, 5 ≤ n → (a n : ℤ) = 6 * a (n - 2) - a (n - 4) + 2) := by
  entry a hmono hset 28 6 7 8 8 20 15

/-- **A154154** (c = 30): Mathar's recurrence and generating function, as printed on the entry,
for any `a` listing {k : 30 + k(k+1)/2 is a square} in increasing order from index 1. -/
theorem a154154 (a : ℕ → ℕ) (hmono : ∀ n, 1 ≤ n → a n < a (n + 1))
    (hset : ∀ k, (∃ m, 30 + k * (k + 1) / 2 = m ^ 2) ↔ ∃ n, 1 ≤ n ∧ a n = k) :
    (a 1 = 3 ∧ a 2 = 13 ∧ a 3 = 34 ∧ a 4 = 84 ∧ a 5 = 203) ∧
    (∀ n, 6 ≤ n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    (X - 1) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) *
        mk (fun n => if n = 0 then (0 : ℤ) else a n) =
      X * (-3 - 10 * X - 3 * X ^ 2 + 10 * X ^ 3 + 4 * X ^ 4) ∧
    (∀ n, 5 ≤ n → (a n : ℤ) = 6 * a (n - 2) - a (n - 4) + 2) := by
  entry a hmono hset 30 3 6 13 11 21 16

/-- The hypotheses are satisfiable: for each of the eight values of c, `listing c` meets them. -/
example : ∀ c ∈ ({8, 10, 13, 21, 24, 25, 28, 30} : Finset ℕ),
    (∀ n, 1 ≤ n → listing c n < listing c (n + 1)) ∧
    (∀ k, S c k ↔ ∃ n, 1 ≤ n ∧ listing c n = k) := by
  intro c hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact listing_spec (k0 := 1) (by norm_num) ⟨3, by norm_num⟩
  · exact listing_spec (k0 := 3) (by norm_num) ⟨4, by norm_num⟩
  · exact listing_spec (k0 := 2) (by norm_num) ⟨4, by norm_num⟩
  · exact listing_spec (k0 := 5) (by norm_num) ⟨6, by norm_num⟩
  · exact listing_spec (k0 := 1) (by norm_num) ⟨5, by norm_num⟩
  · exact listing_spec (k0 := 0) (by norm_num) ⟨5, by norm_num⟩
  · exact listing_spec (k0 := 6) (by norm_num) ⟨7, by norm_num⟩
  · exact listing_spec (k0 := 3) (by norm_num) ⟨6, by norm_num⟩

end A154153
