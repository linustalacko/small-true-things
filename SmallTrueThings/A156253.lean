/-
A156253: a nested recurrence for the run numbers of the Kolakoski sequence.

The Kolakoski sequence A000002 is 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 2, ...:
it consists of 1's and 2's, starts with 1, and its n-th term is the length of its n-th
run. A054353 are its partial sums, so A054353(k) is the position where run k ends.
A156253(n) is the least k with A054353(k) >= n: the number of the run that position n
lies in. It begins 1, 2, 2, 3, 3, 4, 5, 6, 6, 7, 8, 8, 9, 9, ...

The entry A156253 carries this comment, dated Dec 09 2021:

  Conjecture: a(n) = (a(a(n-1)) mod 2) + a(n-2) + 1. - Jon Maiga

Maiga's 2025 note linked from the entry proves the sibling formula
a(n) = a(n - gcd(a(a(n-1)), 2)) + 1 and says a proof of the conjecture "can be
constructed in a similar way". This file proves both, from the definitions above.

`A156253.maiga` is the conjecture and `A156253.maiga_gcd` the sibling formula, for any
`K` that is a Kolakoski sequence (`IsKolakoski`) and any `a` that is its run number.
`A156253.kol` and `A156253.run` are such a `K` and `a`, built from the recurrence
itself, so the hypotheses are not contradictory.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

open Finset

namespace A156253

/-! ### Partial sums and the definition of a Kolakoski sequence -/

/-- A054353 for a sequence `K` indexed from 1: `S K k = K 1 + ⋯ + K k`. If `K k` is the
length of the k-th run, this is the position where the k-th run ends. -/
def S (K : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ Icc 1 k, K i

@[simp] lemma S_zero (K : ℕ → ℕ) : S K 0 = 0 := by simp [S]

lemma S_succ (K : ℕ → ℕ) (k : ℕ) : S K (k + 1) = S K k + K (k + 1) := by
  unfold S
  rw [sum_Icc_succ_top (by omega)]

lemma S_mono (K : ℕ → ℕ) : Monotone (S K) :=
  monotone_nat_of_le_succ fun k => by rw [S_succ]; omega

/-- `K`, indexed from 1, is a Kolakoski sequence: its terms are 1 or 2, and it is cut
into runs, the k-th of length `K k` (so it occupies positions `S K (k-1) + 1, …, S K k`)
and made of 1's when k is odd and 2's when k is even. -/
structure IsKolakoski (K : ℕ → ℕ) : Prop where
  one_or_two : ∀ p, 1 ≤ p → K p = 1 ∨ K p = 2
  runs : ∀ k p, 1 ≤ k → S K (k - 1) < p → p ≤ S K k → K p = if k % 2 = 1 then 1 else 2

/-! ### The recurrences, for any Kolakoski sequence and its run numbers -/

section Abstract

variable {K a : ℕ → ℕ}

/-- Position `n` lies in run `a n`. -/
lemma run_bounds (aleast : ∀ n, 1 ≤ n → IsLeast {k | n ≤ S K k} (a n)) (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ a n ∧ S K (a n - 1) < n ∧ n ≤ S K (a n) := by
  have h1 : n ≤ S K (a n) := (aleast n hn).1
  have h0 : a n ≠ 0 := by
    intro h
    rw [h, S_zero] at h1
    omega
  refine ⟨by omega, ?_, h1⟩
  by_contra hcon
  have : a n ≤ a n - 1 :=
    (aleast n hn).2 (show a n - 1 ∈ {k | n ≤ S K k} from not_lt.mp hcon)
  omega

/-- A run that contains position `n` is run `a n`. -/
lemma run_unique (aleast : ∀ n, 1 ≤ n → IsLeast {k | n ≤ S K k} (a n)) (n k : ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) (h1 : S K (k - 1) < n) (h2 : n ≤ S K k) : a n = k := by
  have hle : a n ≤ k := (aleast n hn).2 (show k ∈ {k | n ≤ S K k} from h2)
  have h3 : n ≤ S K (a n) := (aleast n hn).1
  by_contra hne
  have hlt : a n ≤ k - 1 := by omega
  have := S_mono K hlt
  omega

/-- What happens at position `n`, by the length of the run of position `n - 1`: if that
run has length 1 (its number `a (n-1)` lies in an odd run), position `n` starts a new run
and so did `n - 1`; if it has length 2, position `n` is one run after position `n - 2`. -/
lemma step (hK : IsKolakoski K) (aleast : ∀ n, 1 ≤ n → IsLeast {k | n ≤ S K k} (a n))
    (n : ℕ) (hn : 3 ≤ n) :
    (a (a (n - 1)) % 2 = 1 ∧ a n = a (n - 1) + 1 ∧ a (n - 1) = a (n - 2) + 1) ∨
    (a (a (n - 1)) % 2 = 0 ∧ a n = a (n - 2) + 1) := by
  obtain ⟨hj1, hjl, hju⟩ := run_bounds aleast (n - 1) (by omega)
  obtain ⟨j, hj⟩ : ∃ j, a (n - 1) = j + 1 := ⟨a (n - 1) - 1, by omega⟩
  rw [hj] at hjl hju ⊢
  rw [Nat.add_sub_cancel] at hjl
  have h0 := S_zero K
  have hSj := S_succ K j
  have hSj' := S_succ K (j + 1)
  have hKj := hK.one_or_two (j + 1) (by omega)
  have hKj' := hK.one_or_two (j + 1 + 1) (by omega)
  -- the value at position `j + 1` is decided by the parity of its run
  obtain ⟨hr1, hrl, hru⟩ := run_bounds aleast (j + 1) (by omega)
  have hpar := hK.runs (a (j + 1)) (j + 1) hr1 hrl hru
  -- when run `j + 1` does not start at position 1 or 2, there is a run before it
  have before : S K j = n - 2 → a (n - 2) = j := by
    intro hS
    have hj0 : j ≠ 0 := by
      rintro rfl
      omega
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hSi := S_succ K i
    have hKi := hK.one_or_two (i + 1) (by omega)
    exact run_unique aleast (n - 2) (i + 1) (by omega) (by omega)
      (by rw [Nat.add_sub_cancel]; omega) (by omega)
  rcases hKj with h | h
  · left
    have hodd : a (j + 1) % 2 = 1 := by
      by_contra hc
      rw [ite_eq_right hc] at hpar
      omega
    have hn1 : a n = j + 1 + 1 :=
      run_unique aleast n (j + 1 + 1) (by omega) (by omega)
        (by rw [Nat.add_sub_cancel]; omega) (by omega)
    have hn2 := before (by omega)
    exact ⟨hodd, by omega, by omega⟩
  · right
    have heven : a (j + 1) % 2 = 0 := by
      by_contra hc
      have h1 : a (j + 1) % 2 = 1 := by omega
      rw [ite_eq_left h1] at hpar
      omega
    refine ⟨heven, ?_⟩
    rcases (by omega : S K j = n - 2 ∨ S K j = n - 3) with h2 | h3
    · have hn1 : a n = j + 1 :=
        run_unique aleast n (j + 1) (by omega) (by omega)
          (by rw [Nat.add_sub_cancel]; omega) (by omega)
      have hn2 := before h2
      omega
    · have hn1 : a n = j + 1 + 1 :=
        run_unique aleast n (j + 1 + 1) (by omega) (by omega)
          (by rw [Nat.add_sub_cancel]; omega) (by omega)
      have hn2 : a (n - 2) = j + 1 :=
        run_unique aleast (n - 2) (j + 1) (by omega) (by omega)
          (by rw [Nat.add_sub_cancel]; omega) (by omega)
      omega

/-- **Maiga's conjecture on A156253.** For a Kolakoski sequence `K` and its run numbers
`a`: `a(n) = (a(a(n-1)) mod 2) + a(n-2) + 1` for `n ≥ 3`. -/
theorem maiga (K a : ℕ → ℕ) (hK : IsKolakoski K)
    (aleast : ∀ n, 1 ≤ n → IsLeast {k | n ≤ S K k} (a n)) :
    ∀ n, 3 ≤ n → a n = a (a (n - 1)) % 2 + a (n - 2) + 1 := by
  intro n hn
  rcases step hK aleast n hn with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ <;> omega

/-- The first two run numbers are 1 and 2. -/
lemma first_two (hK : IsKolakoski K) (aleast : ∀ n, 1 ≤ n → IsLeast {k | n ≤ S K k} (a n)) :
    a 1 = 1 ∧ a 2 = 2 := by
  have h0 := S_zero K
  have hS1 : S K 1 = S K 0 + K 1 := S_succ K 0
  have hS2 : S K 2 = S K 1 + K 2 := S_succ K 1
  have hK1 := hK.one_or_two 1 le_rfl
  have hK2 := hK.one_or_two 2 (by omega)
  have hK1' : K 1 = 1 := by
    have := hK.runs 1 1 le_rfl (show S K (1 - 1) < 1 by simp) (show 1 ≤ S K 1 by omega)
    simpa using this
  have h1 : a 1 = 1 :=
    run_unique aleast 1 1 le_rfl le_rfl (show S K (1 - 1) < 1 by simp) (show 1 ≤ S K 1 by omega)
  have h2 : a 2 = 2 :=
    run_unique aleast 2 2 (by omega) (by omega) (show S K 1 < 2 by omega)
      (show 2 ≤ S K 2 by omega)
  exact ⟨h1, h2⟩

/-- **The sibling recurrence** (Maiga 2023, proved in his 2025 note):
`a(n) = a(n - gcd(a(a(n-1)), 2)) + 1` for `n ≥ 2`. -/
theorem maiga_gcd (K a : ℕ → ℕ) (hK : IsKolakoski K)
    (aleast : ∀ n, 1 ≤ n → IsLeast {k | n ≤ S K k} (a n)) :
    ∀ n, 2 ≤ n → a n = a (n - Nat.gcd (a (a (n - 1))) 2) + 1 := by
  intro n hn
  have gcd_two : ∀ x : ℕ, Nat.gcd x 2 = if x % 2 = 1 then 1 else 2 := by
    intro x
    rw [Nat.gcd_comm, Nat.gcd_rec]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]
  obtain ⟨h1, h2⟩ := first_two hK aleast
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · obtain rfl : n = 2 := by omega
    rw [gcd_two]
    simp [h1, h2]
  · rw [gcd_two]
    rcases step hK aleast n hge with ⟨e1, e2, e3⟩ | ⟨e1, e2⟩
    · rw [ite_eq_left e1, e2]
    · rw [ite_eq_right (by omega), e2]

end Abstract

/-! ### A Kolakoski sequence, built from the recurrence -/

/-- The run numbers, by the recurrence of the conjecture. The `min` only makes the
definition visibly terminate; `run n ≤ n` always, so it changes nothing (`run_rec`). -/
def run : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 => run (min (run (n + 2)) (n + 2)) % 2 + run (n + 1) + 1
termination_by n => n
decreasing_by all_goals omega

/-- The Kolakoski sequence: 1 where the run number is odd, 2 where it is even. -/
def kol (p : ℕ) : ℕ := if run p % 2 = 1 then 1 else 2

lemma kol_one_or_two (p : ℕ) : kol p = 1 ∨ kol p = 2 := by
  unfold kol
  split <;> simp

lemma S_kol_strictMono : StrictMono (S kol) :=
  strictMono_nat_of_lt_succ fun k => by
    rw [S_succ]
    have := kol_one_or_two (k + 1)
    omega

lemma le_S_kol (k : ℕ) : k ≤ S kol k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [S_succ]
    have := kol_one_or_two (k + 1)
    omega

/-- Position `n` lies in run `run n` of `kol`. -/
lemma run_spec : ∀ n, 1 ≤ n → 1 ≤ run n ∧ S kol (run n - 1) < n ∧ n ≤ S kol (run n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have r1 : run 1 = 1 := by rw [run]
    have r2 : run 2 = 2 := by rw [run]
    have h0 := S_zero kol
    have hS1 : S kol 1 = S kol 0 + kol 1 := S_succ kol 0
    have hS2 : S kol 2 = S kol 1 + kol 2 := S_succ kol 1
    have k1 : kol 1 = 1 := by simp [kol, r1]
    have k2 : kol 2 = 2 := by simp [kol, r2]
    rcases (by omega : n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | h3
    · rw [r1]
      exact ⟨le_rfl, by simp, by omega⟩
    · rw [r2]
      exact ⟨by omega, show S kol 1 < 2 by omega, by omega⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      obtain ⟨hj1, hjl, hju⟩ := ih (m + 2) (by omega) (by omega)
      obtain ⟨hi1, hil, hiu⟩ := ih (m + 1) (by omega) (by omega)
      obtain ⟨j, hj⟩ : ∃ j, run (m + 2) = j + 1 := ⟨run (m + 2) - 1, by omega⟩
      obtain ⟨i, hi⟩ : ∃ i, run (m + 1) = i + 1 := ⟨run (m + 1) - 1, by omega⟩
      rw [hj, Nat.add_sub_cancel] at hjl
      rw [hj] at hju
      rw [hi, Nat.add_sub_cancel] at hil
      rw [hi] at hiu
      have hjm : j + 1 ≤ m + 2 := by
        have := le_S_kol j
        omega
      have hrun : run (m + 3) = run (j + 1) % 2 + (i + 1) + 1 := by
        rw [run, hj, hi, Nat.min_eq_left hjm]
      -- consecutive positions lie in the same run or in consecutive runs
      have hji : j ≤ i + 1 :=
        S_kol_strictMono.le_iff_le.mp (by omega : S kol j ≤ S kol (i + 1))
      have hij : i < j + 1 :=
        S_kol_strictMono.lt_iff_lt.mp (by omega : S kol i < S kol (j + 1))
      have hkol : kol (j + 1) = if run (j + 1) % 2 = 1 then 1 else 2 := rfl
      have hSi := S_succ kol i
      have hSi1 := S_succ kol (i + 1)
      have hSi2 := S_succ kol (i + 1 + 1)
      have hKi1 := kol_one_or_two (i + 1)
      have hKi2 := kol_one_or_two (i + 1 + 1)
      have hKi3 := kol_one_or_two (i + 1 + 1 + 1)
      rw [hrun]
      rcases (by omega : j = i + 1 ∨ j = i) with rfl | rfl
      · by_cases he : run (i + 1 + 1) % 2 = 1
        · rw [ite_eq_left he] at hkol
          rw [he]
          refine ⟨by omega, ?_, ?_⟩
          · rw [show 1 + (i + 1) + 1 - 1 = i + 1 + 1 by omega]
            omega
          · rw [show 1 + (i + 1) + 1 = i + 1 + 1 + 1 by omega]
            omega
        · rw [ite_eq_right he] at hkol
          have he0 : run (i + 1 + 1) % 2 = 0 := by omega
          rw [he0]
          refine ⟨by omega, ?_, ?_⟩
          · rw [show 0 + (i + 1) + 1 - 1 = i + 1 by omega]
            omega
          · rw [show 0 + (i + 1) + 1 = i + 1 + 1 by omega]
            omega
      · by_cases he : run (j + 1) % 2 = 1
        · rw [ite_eq_left he] at hkol
          omega
        · rw [ite_eq_right he] at hkol
          have he0 : run (j + 1) % 2 = 0 := by omega
          rw [he0]
          refine ⟨by omega, ?_, ?_⟩
          · rw [show 0 + (j + 1) + 1 - 1 = j + 1 by omega]
            omega
          · rw [show 0 + (j + 1) + 1 = j + 1 + 1 by omega]
            omega

/-- `kol` is a Kolakoski sequence. -/
theorem kol_isKolakoski : IsKolakoski kol where
  one_or_two := fun p _ => kol_one_or_two p
  runs := by
    intro k p hk h1 h2
    obtain ⟨hr1, hrl, hru⟩ := run_spec p (by omega)
    have a1 := S_kol_strictMono.lt_iff_lt.mp (lt_of_lt_of_le hrl h2)
    have a2 := S_kol_strictMono.lt_iff_lt.mp (lt_of_lt_of_le h1 hru)
    have hrk : run p = k := by omega
    unfold kol
    rw [hrk]

/-- `run n` is the least `k` with `n ≤ S kol k`: the A156253 of `kol`. -/
theorem run_isLeast (n : ℕ) (hn : 1 ≤ n) : IsLeast {k | n ≤ S kol k} (run n) := by
  obtain ⟨hr1, hrl, hru⟩ := run_spec n hn
  refine ⟨hru, fun k hk => ?_⟩
  have hk' : n ≤ S kol k := hk
  by_contra hcon
  have hlt : k ≤ run n - 1 := by omega
  have := S_kol_strictMono.monotone hlt
  omega

/-- The conjecture for the concrete sequence: the recurrence without the `min`. -/
theorem run_rec (n : ℕ) (hn : 3 ≤ n) : run n = run (run (n - 1)) % 2 + run (n - 2) + 1 :=
  maiga kol run kol_isKolakoski run_isLeast n hn

/-- The first twelve terms are those of A000002. -/
example : (List.range 12).map (fun i => kol (i + 1)) = [1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2] := by
  simp [kol, run, List.range, List.range.loop]

end A156253
