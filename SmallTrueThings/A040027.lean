/-
A040027: the Gould numbers as a Stirling transform of the alternating factorials.

The OEIS entry A040027 (the Gould numbers 1, 1, 3, 9, 31, 121, 523, ...) carries this
comment, dated Aug 31 2021:

  Conjecture: a(n) = Sum_{k = 0..n} A058006(k)*A048993(n+1, k+1) - Velin Yanev

A058006(k) = 0! - 1! + 2! - ... + (-1)^k k! are the alternating factorials and
A048993 is the triangle of Stirling numbers of the second kind.

The entry gives the Gould numbers by this recurrence (Jon Perry, 2005):
  a(0) = 1, a(1) = 1, and a(n) = n + Sum_{j=1..n-1} binomial(n, j+1)*a(j) for n > 1.

`A040027.yanev` proves the conjecture for any `a` satisfying exactly that recurrence.
`A040027.gould` is such an `a`, so the recurrence is not contradictory, and
`A040027.gould_eq` is the statement for it.
-/
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

open Finset Nat

namespace A040027

/-! ### Two identities for Stirling numbers of the second kind -/

/-- Remove the block containing the last element: if it has `n - j` other elements,
the remaining `j` elements form `m` blocks. -/
lemma stirlingSecond_succ_succ_eq_sum_choose (n m : ℕ) :
    stirlingSecond (n + 1) (m + 1) = ∑ j ∈ range (n + 1), n.choose j * stirlingSecond j m := by
  induction n generalizing m with
  | zero => simp [stirlingSecond_succ_succ, stirlingSecond_zero_succ]
  | succ n ih =>
    have shift : ∑ j ∈ range (n + 1), n.choose (j + 1) * stirlingSecond (j + 1) m
        + stirlingSecond 0 m = stirlingSecond (n + 1) (m + 1) := by
      have h1 := sum_range_succ (fun j => n.choose j * stirlingSecond j m) (n + 1)
      rw [sum_range_succ' (fun j => n.choose j * stirlingSecond j m) (n + 1)] at h1
      simp only [choose_succ_self, zero_mul, add_zero, choose_zero_right, one_mul] at h1
      rw [h1, ← ih m]
    have split : ∑ j ∈ range (n + 1 + 1), (n + 1).choose j * stirlingSecond j m
        = ∑ j ∈ range (n + 1), n.choose j * stirlingSecond (j + 1) m
          + stirlingSecond (n + 1) (m + 1) := by
      rw [sum_range_succ' (fun j => (n + 1).choose j * stirlingSecond j m) (n + 1), ← shift,
        choose_zero_right, one_mul, ← add_assoc, ← sum_add_distrib]
      congr 1
      refine sum_congr rfl fun j _ => ?_
      rw [choose_succ_succ', add_mul]
    rw [split]
    cases m with
    | zero =>
      rw [stirlingSecond_succ_succ (n + 1) 0]
      simp [stirlingSecond_succ_zero]
    | succ m =>
      have h : ∑ j ∈ range (n + 1), n.choose j * stirlingSecond (j + 1) (m + 1)
          = (m + 1) * stirlingSecond (n + 1) (m + 1 + 1) + stirlingSecond (n + 1) (m + 1) := by
        rw [ih (m + 1), ih m, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun j _ => ?_
        rw [stirlingSecond_succ_succ]
        ring
      rw [h, stirlingSecond_succ_succ (n + 1) (m + 1)]
      ring

/-- The alternating sum `Σ (-1)^k k! S(n+1, k+1)` vanishes for `n ≥ 1`. -/
lemma alternating_sum (n : ℕ) :
    ∑ k ∈ range (n + 1 + 1),
      (-1 : ℤ) ^ k * (k ! : ℤ) * (stirlingSecond (n + 1 + 1) (k + 1) : ℤ) = 0 := by
  have step : ∀ k : ℕ, (-1 : ℤ) ^ k * (k ! : ℤ) * (stirlingSecond (n + 1 + 1) (k + 1) : ℤ)
      = (-1) ^ k * ((k + 1)! : ℤ) * (stirlingSecond (n + 1) (k + 1) : ℤ)
        + (-1) ^ k * (k ! : ℤ) * (stirlingSecond (n + 1) k : ℤ) := by
    intro k
    rw [stirlingSecond_succ_succ, factorial_succ]
    push_cast
    ring
  simp_rw [step]
  rw [sum_add_distrib,
    sum_range_succ (fun k => (-1 : ℤ) ^ k * ((k + 1)! : ℤ) * (stirlingSecond (n + 1) (k + 1) : ℤ)),
    sum_range_succ' (fun k => (-1 : ℤ) ^ k * (k ! : ℤ) * (stirlingSecond (n + 1) k : ℤ)),
    stirlingSecond_eq_zero_of_lt (by omega : n + 1 < n + 1 + 1), stirlingSecond_succ_zero]
  simp only [Nat.cast_zero, mul_zero, add_zero]
  rw [← sum_add_distrib]
  refine sum_eq_zero fun k _ => ?_
  ring

/-! ### The conjecture -/

/-- A058006: the alternating factorials `0! - 1! + 2! - ... + (-1)^k k!`. -/
def altFactorial (k : ℕ) : ℤ := ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * (j ! : ℤ)

lemma altFactorial_succ (k : ℕ) :
    altFactorial (k + 1) = altFactorial k + (-1 : ℤ) ^ (k + 1) * ((k + 1)! : ℤ) :=
  sum_range_succ _ _

/-- The right side of the conjecture. -/
def rhs (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), altFactorial k * (stirlingSecond (n + 1) (k + 1) : ℤ)

lemma rhs_zero : rhs 0 = 1 := by simp [rhs, altFactorial, stirlingSecond_self]

/-- The right side obeys the Gould recurrence `a(n) = Σ_{i<n} C(n, i+1) a(i)`. -/
lemma rhs_rec (n : ℕ) (hn : 1 ≤ n) :
    rhs n = ∑ i ∈ range n, (n.choose (i + 1) : ℤ) * rhs i := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  -- the sum of the earlier terms, by the first identity
  have hR : ∑ i ∈ range (n + 1), ((n + 1).choose (i + 1) : ℤ) * rhs i
      = ∑ k ∈ range (n + 1),
          altFactorial k * (stirlingSecond (n + 1 + 1) (k + 1 + 1) : ℤ) := by
    have ext : ∀ i ∈ range (n + 1), rhs i
        = ∑ k ∈ range (n + 1), altFactorial k * (stirlingSecond (i + 1) (k + 1) : ℤ) := by
      intro i hi
      refine sum_subset (range_mono (by have := mem_range.mp hi; omega)) fun k _ hk => ?_
      rw [stirlingSecond_eq_zero_of_lt (by simp only [mem_range] at hk; omega)]
      simp
    rw [sum_congr rfl fun i hi => by rw [ext i hi]]
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    have h := stirlingSecond_succ_succ_eq_sum_choose (n + 1) (k + 1)
    rw [sum_range_succ' (fun j => (n + 1).choose j * stirlingSecond j (k + 1)) (n + 1),
      stirlingSecond_zero_succ, mul_zero, add_zero] at h
    rw [h]
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    ring
  -- the term itself, split by `altFactorial_succ`
  have hL : rhs (n + 1)
      = ∑ k ∈ range (n + 1), altFactorial k * (stirlingSecond (n + 1 + 1) (k + 1 + 1) : ℤ)
        + ∑ k ∈ range (n + 1 + 1),
            (-1 : ℤ) ^ k * (k ! : ℤ) * (stirlingSecond (n + 1 + 1) (k + 1) : ℤ) := by
    unfold rhs
    rw [sum_range_succ' (fun k => altFactorial k * (stirlingSecond (n + 1 + 1) (k + 1) : ℤ)),
      sum_range_succ'
        (fun k => (-1 : ℤ) ^ k * (k ! : ℤ) * (stirlingSecond (n + 1 + 1) (k + 1) : ℤ)),
      ← add_assoc, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    rw [altFactorial_succ]
    ring
  rw [hL, alternating_sum, add_zero, hR]

/-- **Yanev's conjecture on A040027.** If `a` obeys the Gould recurrence, then
`a(n) = Σ_{k=0..n} A058006(k) * S(n+1, k+1)`. -/
theorem yanev (a : ℕ → ℕ)
    (a0 : a 0 = 1) (a1 : a 1 = 1)
    (arec : ∀ n, 2 ≤ n → a n = n + ∑ j ∈ Icc 1 (n - 1), n.choose (j + 1) * a j) :
    ∀ n, (a n : ℤ)
      = ∑ k ∈ range (n + 1), altFactorial k * (stirlingSecond (n + 1) (k + 1) : ℤ) := by
  -- the recurrence in one piece
  have arec' : ∀ n, 1 ≤ n → a n = ∑ i ∈ range n, n.choose (i + 1) * a i := by
    intro n hn
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      simp [a0, a1]
    · obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [arec (n + 1) h, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), a0,
        Nat.add_sub_cancel]
      simp only [zero_add, choose_one_right, mul_one]
      rfl
  intro n
  change (a n : ℤ) = rhs n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [a0, rhs_zero]
      rfl
    · rw [rhs_rec n hn, arec' n hn]
      push_cast
      refine sum_congr rfl fun i hi => ?_
      rw [ih i (mem_range.mp hi)]

/-! ### A sequence that obeys the recurrence -/

/-- The Gould numbers. -/
def gould (n : ℕ) : ℕ :=
  if n = 0 then 1 else ∑ i : Fin n, n.choose (i + 1) * gould i
termination_by n
decreasing_by exact i.isLt

lemma gould_zero : gould 0 = 1 := by rw [gould]; simp

lemma gould_pos (n : ℕ) (hn : 1 ≤ n) :
    gould n = ∑ i ∈ range n, n.choose (i + 1) * gould i := by
  rw [gould, ite_eq_right (by omega),
    Fin.sum_univ_eq_sum_range (fun i => n.choose (i + 1) * gould i)]

lemma gould_one : gould 1 = 1 := by simp [gould_pos 1 le_rfl, gould_zero]

lemma gould_rec (n : ℕ) (hn : 2 ≤ n) :
    gould n = n + ∑ j ∈ Icc 1 (n - 1), n.choose (j + 1) * gould j := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [gould_pos (n + 1) (by omega), range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega),
    gould_zero, Nat.add_sub_cancel]
  simp only [zero_add, choose_one_right, mul_one]
  rfl

/-- Yanev's conjecture for the Gould numbers. -/
theorem gould_eq (n : ℕ) :
    (gould n : ℤ)
      = ∑ k ∈ range (n + 1), altFactorial k * (stirlingSecond (n + 1) (k + 1) : ℤ) :=
  yanev gould gould_zero gould_one gould_rec n

/-- The right side begins 1, 1, 3, 9, 31, 121, 523, as the Gould numbers do. -/
example : (List.range 7).map rhs = [1, 1, 3, 9, 31, 121, 523] := by decide

end A040027
