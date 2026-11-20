/-
A005121: Mohapatra's triangle for the chains of the partition lattice.

The OEIS entry A005121 (number of chains from bottom to top in the lattice of set
partitions of an n-set; Lengyel's numbers 1, 1, 4, 32, 436, 9012, ...) carries this
comment, dated Oct 30 2026:

  Conjecture: a(n) = R(n,n) where R(1,1) = 1,
  R(n,k) = k * Sum_{j=k..n-1} R(n-1,j) for 1 <= k < n,
  R(n,n) = Sum_{j=1..n-1} R(n,j).  - Rajesh Kumar Mohapatra

The entry's established formula is Lengyel's recurrence
  a(1) = 1,  a(n) = Sum_{k=1..n-1} Stirling2(n,k) * a(k).

`A005121.mohapatra` proves the conjecture for any `R` and `a` satisfying exactly
those rules. `A005121.T` and `A005121.L` are such an `R` and `a`, so the rules are
not contradictory, and `A005121.T_diag_eq_L` is the statement for them.
-/
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

open Finset

namespace A005121

/-! ### Products over multisets of consecutive integers -/

/-- `H d k m` is the sum, over all multisets of `d` integers taken from `k, k+1, …, m`,
of the product of the multiset: the complete homogeneous symmetric polynomial of
degree `d` at `k, …, m`. A multiset of `d + 1` integers is its least element `j`
and a multiset of `d` integers from `j, …, m`. -/
def H : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | d + 1, k, m => ∑ j ∈ Icc k m, j * H d j m

@[simp] lemma H_zero (k m : ℕ) : H 0 k m = 1 := by rw [H]

lemma H_succ (d k m : ℕ) : H (d + 1) k m = ∑ j ∈ Icc k m, j * H d j m := by rw [H]

/-- A multiset either contains the top value `m + 1` or it does not. -/
lemma H_succ_top (d k m : ℕ) (hk : k ≤ m + 1) :
    H (d + 1) k (m + 1) = (m + 1) * H d k (m + 1) + H (d + 1) k m := by
  induction d generalizing k with
  | zero =>
    simp only [H_succ, H_zero, mul_one]
    rw [sum_Icc_succ_top hk]
    ring
  | succ d ih =>
    rw [H_succ (d + 1) k (m + 1), sum_Icc_succ_top hk]
    have h1 : ∑ j ∈ Icc k m, j * H (d + 1) j (m + 1)
        = (m + 1) * ∑ j ∈ Icc k m, j * H d j (m + 1)
          + ∑ j ∈ Icc k m, j * H (d + 1) j m := by
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun j hj => ?_
      rw [ih j (by have := (mem_Icc.mp hj).2; omega)]
      ring
    have h2 : H (d + 1) (m + 1) (m + 1) = (m + 1) * H d (m + 1) (m + 1) := by
      rw [H_succ, Icc_self, sum_singleton]
    rw [h1, h2, H_succ d k (m + 1), sum_Icc_succ_top hk, H_succ (d + 1) k m]
    ring

/-- Stirling numbers of the second kind are these sums over `1, …, m`. -/
lemma stirlingSecond_eq_H (d m : ℕ) : Nat.stirlingSecond (m + d) m = H d 1 m := by
  induction d generalizing m with
  | zero => simp [Nat.stirlingSecond_self]
  | succ d ihd =>
    induction m with
    | zero => simp [H_succ, Nat.stirlingSecond_succ_zero]
    | succ m ihm =>
      have e1 : m + 1 + (d + 1) = (m + 1 + d) + 1 := by ring
      have e2 : m + 1 + d = m + (d + 1) := by ring
      rw [e1, Nat.stirlingSecond_succ_succ, ihd (m + 1), H_succ_top d 1 m (by omega), e2, ihm]

/-! ### The conjecture, for any triangle obeying the rules -/

section Abstract

variable {R : ℕ → ℕ → ℕ}

/-- Below the diagonal, row `n + 1` is a combination of the diagonal entries above it. -/
lemma off_diagonal
    (R11 : R 1 1 = 1)
    (Roff : ∀ n k, 1 ≤ k → k < n → R n k = k * ∑ j ∈ Icc k (n - 1), R (n - 1) j)
    (n : ℕ) (hn : 1 ≤ n) :
    ∀ k, 1 ≤ k → k ≤ n →
      R (n + 1) k = ∑ m ∈ Icc k n, R m m * (k * H (n - m) k m) := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro k hk1 hk
    obtain rfl : k = 1 := by omega
    rw [Roff (1 + 1) 1 (by norm_num) (by norm_num)]
    simp [R11]
  | succ n hn ih =>
    intro k hk1 hk
    rw [Roff (n + 1 + 1) k hk1 (by omega), Nat.add_sub_cancel,
      sum_Icc_succ_top hk, sum_Icc_succ_top hk]
    have key : ∑ j ∈ Icc k n, R (n + 1) j = ∑ m ∈ Icc k n, R m m * H (n - m + 1) k m := by
      calc ∑ j ∈ Icc k n, R (n + 1) j
          = ∑ j ∈ Icc k n, ∑ m ∈ Icc j n, R m m * (j * H (n - m) j m) :=
            sum_congr rfl fun j hj =>
              ih j (by have := (mem_Icc.mp hj).1; omega) (mem_Icc.mp hj).2
        _ = ∑ m ∈ Icc k n, ∑ j ∈ Icc k m, R m m * (j * H (n - m) j m) :=
            sum_comm' (by intro j m; simp only [mem_Icc]; omega)
        _ = ∑ m ∈ Icc k n, R m m * H (n - m + 1) k m :=
            sum_congr rfl fun m _ => by rw [H_succ, mul_sum]
    rw [key, mul_add, mul_sum]
    congr 1
    · refine sum_congr rfl fun m hm => ?_
      have : n + 1 - m = n - m + 1 := by have := (mem_Icc.mp hm).2; omega
      rw [this]
      ring
    · simp [mul_comm]

/-- The diagonal of the triangle obeys Lengyel's recurrence. -/
theorem diagonal_recurrence
    (R11 : R 1 1 = 1)
    (Roff : ∀ n k, 1 ≤ k → k < n → R n k = k * ∑ j ∈ Icc k (n - 1), R (n - 1) j)
    (Rdiag : ∀ n, 2 ≤ n → R n n = ∑ j ∈ Icc 1 (n - 1), R n j)
    (n : ℕ) (hn : 2 ≤ n) :
    R n n = ∑ m ∈ Icc 1 (n - 1), Nat.stirlingSecond n m * R m m := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hn' : 1 ≤ n := by omega
  rw [Rdiag (n + 1) hn, Nat.add_sub_cancel]
  calc ∑ k ∈ Icc 1 n, R (n + 1) k
      = ∑ k ∈ Icc 1 n, ∑ m ∈ Icc k n, R m m * (k * H (n - m) k m) :=
        sum_congr rfl fun k hk =>
          off_diagonal R11 Roff n hn' k (mem_Icc.mp hk).1 (mem_Icc.mp hk).2
    _ = ∑ m ∈ Icc 1 n, ∑ k ∈ Icc 1 m, R m m * (k * H (n - m) k m) :=
        sum_comm' (by intro k m; simp only [mem_Icc]; omega)
    _ = ∑ m ∈ Icc 1 n, Nat.stirlingSecond (n + 1) m * R m m :=
        sum_congr rfl fun m hm => by
          have hm2 := (mem_Icc.mp hm).2
          have e : n + 1 = m + (n - m + 1) := by omega
          rw [e, stirlingSecond_eq_H, H_succ, ← mul_sum]
          exact mul_comm _ _

/-- **Mohapatra's conjecture on A005121.** If `R` is the triangle of the conjecture
and `a` obeys Lengyel's recurrence, then `R n n = a n` for every `n ≥ 1`. -/
theorem mohapatra (R : ℕ → ℕ → ℕ) (a : ℕ → ℕ)
    (R11 : R 1 1 = 1)
    (Roff : ∀ n k, 1 ≤ k → k < n → R n k = k * ∑ j ∈ Icc k (n - 1), R (n - 1) j)
    (Rdiag : ∀ n, 2 ≤ n → R n n = ∑ j ∈ Icc 1 (n - 1), R n j)
    (a1 : a 1 = 1)
    (arec : ∀ n, 2 ≤ n → a n = ∑ k ∈ Icc 1 (n - 1), Nat.stirlingSecond n k * a k) :
    ∀ n, 1 ≤ n → R n n = a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      rw [R11, a1]
    · rw [diagonal_recurrence R11 Roff Rdiag n h, arec n h]
      refine sum_congr rfl fun m hm => ?_
      have := mem_Icc.mp hm
      rw [ih m (by omega) this.1]

end Abstract

/-! ### A triangle and a sequence that obey the rules -/

/-- The triangle of the conjecture, defined row by row; zero outside `1 ≤ k ≤ n`
except where the rules do not look. -/
def T : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, k => if k = 1 then 1 else 0
  | n + 2, k =>
    if k = n + 2 then ∑ i ∈ Icc 1 (n + 1), i * ∑ j ∈ Icc i (n + 1), T (n + 1) j
    else k * ∑ j ∈ Icc k (n + 1), T (n + 1) j

lemma T_one_one : T 1 1 = 1 := by simp [T]

lemma T_off (n k : ℕ) (_hk : 1 ≤ k) (hkn : k < n) :
    T n k = k * ∑ j ∈ Icc k (n - 1), T (n - 1) j := by
  match n, hkn with
  | 0, h => omega
  | 1, h => omega
  | n + 2, h =>
    rw [T, ite_eq_right (by omega)]
    rfl

lemma T_diag (n : ℕ) (hn : 2 ≤ n) : T n n = ∑ j ∈ Icc 1 (n - 1), T n j := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  rw [T, ite_eq_left rfl]
  refine sum_congr rfl fun j hj => ?_
  have := (mem_Icc.mp hj).2
  rw [T, ite_eq_right (by omega)]

/-- Lengyel's numbers, by Lengyel's recurrence. -/
def L (n : ℕ) : ℕ :=
  if n ≤ 1 then n else ∑ k : Fin n, Nat.stirlingSecond n k * L k
termination_by n
decreasing_by exact k.isLt

lemma L_one : L 1 = 1 := by rw [L]; simp

lemma L_rec (n : ℕ) (hn : 2 ≤ n) :
    L n = ∑ k ∈ Icc 1 (n - 1), Nat.stirlingSecond n k * L k := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [L, ite_eq_right (by omega),
    Fin.sum_univ_eq_sum_range (fun k => Nat.stirlingSecond (n + 1) k * L k), range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), Nat.stirlingSecond_succ_zero, zero_mul,
    zero_add, Nat.add_sub_cancel]
  rfl

/-- Mohapatra's conjecture for the concrete triangle and Lengyel's numbers. -/
theorem T_diag_eq_L (n : ℕ) (hn : 1 ≤ n) : T n n = L n :=
  mohapatra T L T_one_one T_off T_diag L_one L_rec n hn

/-- The fifth row ends in 436, the fifth of Lengyel's numbers. -/
example : (List.range 5).map (fun k => T 5 (k + 1)) = [64, 112, 132, 128, 436] := by decide

end A005121
