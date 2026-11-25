/-
A154138: the numbers k for which 3 plus the k-th triangular number is a square.

The OEIS entry A154138 (1, 3, 12, 22, 73, 131, 428, 766, ..., offset 1) is defined as
  {k: 3+k*(k+1)/2 in A000290}
and carries these formulas, marked as conjectures (R. J. Mathar, Oct 18 2009):

  a(n) = +a(n-1) +6*a(n-2) -6*a(n-3) -a(n-4) +a(n-5);
  G.f.: x*(1 + 2*x + 3*x^2 - 2*x^3 - 2*x^4)/((1-x)*(x^2-2*x-1)*(x^2+2*x-1)),

with Zak Seidov's form a(1..4) = (1,3,12,22), a(n>4) = 6*a(n-2) - a(n-4) + 2.

`A154138.mathar` proves all three for any `a` that lists that set in increasing order,
indexed from 1, and `A154138.listing` is such an `a`, so the hypotheses are satisfiable.

The idea. With x = 2k+1, 3 + k(k+1)/2 = y^2 says x^2 + 23 = 8y^2. The map
(x, y) ↦ (3x - 8y, 3y - x) sends a solution with y ≥ 6 to one with a smaller positive y,
so every solution climbs from (3, 2) or (7, 3) by the inverse map (x, y) ↦ (3x + 8y, x + 3y).
Taken alternately, the two chains are already in increasing order.
-/
import Mathlib

open PowerSeries

namespace A154138

/-- The set of the entry: 3 plus the k-th triangular number is a square. -/
def S (k : ℕ) : Prop := ∃ m, 3 + k * (k + 1) / 2 = m ^ 2

/-- Multiplication by the unit 3 + √8. -/
def step (p : ℕ × ℕ) : ℕ × ℕ := (3 * p.1 + 8 * p.2, p.1 + 3 * p.2)

/-- The solutions of x^2 + 23 = 8y^2 in increasing order: the chains from (3, 2) and
(7, 3), interleaved. -/
def sol : ℕ → ℕ × ℕ
  | 0 => (3, 2)
  | 1 => (7, 3)
  | n + 2 => step (sol n)

/-- The listing: k = (x - 1)/2, indexed from 0. -/
def b (n : ℕ) : ℕ := ((sol n).1 - 1) / 2

lemma step_eq {x y : ℕ} (h : x ^ 2 + 23 = 8 * y ^ 2) :
    (step (x, y)).1 ^ 2 + 23 = 8 * (step (x, y)).2 ^ 2 := by
  simp only [step]
  nlinarith [h]

/-- Every term is a solution, and its x is odd. -/
lemma sol_spec (n : ℕ) : (sol n).1 ^ 2 + 23 = 8 * (sol n).2 ^ 2 ∧ (sol n).1 % 2 = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => decide
    | 1, _ => decide
    | n + 2, ih =>
      obtain ⟨h1, h2⟩ := ih n (by omega)
      have hp : sol n = ((sol n).1, (sol n).2) := rfl
      refine ⟨?_, ?_⟩
      · show (step (sol n)).1 ^ 2 + 23 = 8 * (step (sol n)).2 ^ 2
        rw [hp]; exact step_eq h1
      · show (3 * (sol n).1 + 8 * (sol n).2) % 2 = 1
        omega

/-- The descent: every solution is a term. -/
lemma sol_complete : ∀ y x : ℕ, x ^ 2 + 23 = 8 * y ^ 2 → ∃ n, sol n = (x, y) := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro x h
    by_cases hy : y ≤ 5
    · have hx : x ≤ 13 := by nlinarith
      interval_cases y <;> interval_cases x <;> simp_all
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · push Not at hy
      have h1 : 8 * y ≤ 3 * x := by
        by_contra hc; push Not at hc; nlinarith
      have h2 : x ≤ 3 * y := by
        by_contra hc; push Not at hc; nlinarith
      have h3 : 2 * y < x := by
        by_contra hc; push Not at hc; nlinarith
      obtain ⟨x', hx'⟩ : ∃ x', x' = 3 * x - 8 * y := ⟨_, rfl⟩
      obtain ⟨y', hy'⟩ : ∃ y', y' = 3 * y - x := ⟨_, rfl⟩
      have ex : x = 3 * x' + 8 * y' := by omega
      have ey : y = x' + 3 * y' := by omega
      have h' : x' ^ 2 + 23 = 8 * y' ^ 2 := by
        subst ex ey; nlinarith [h]
      obtain ⟨n, hn⟩ := ih y' (by omega) x' h'
      refine ⟨n + 2, ?_⟩
      show step (sol n) = (x, y)
      rw [hn, ex, ey]; rfl

/-- The terms increase, and each lies below the next one's chain-predecessor's image. -/
lemma sol_order (n : ℕ) :
    ((sol n).1 < (sol (n + 1)).1 ∧ (sol n).2 < (sol (n + 1)).2) ∧
    ((sol (n + 1)).1 < (step (sol n)).1 ∧ (sol (n + 1)).2 < (step (sol n)).2) := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨⟨a1, a2⟩, b1, b2⟩ := ih
    refine ⟨⟨b1, b2⟩, ?_, ?_⟩
    · show (step (sol n)).1 < (step (sol (n + 1))).1
      simp only [step]; omega
    · show (step (sol n)).2 < (step (sol (n + 1))).2
      simp only [step]; omega

lemma b_strictMono : StrictMono b := by
  apply strictMono_nat_of_lt_succ
  intro n
  have := (sol_order n).1.1
  have h0 := (sol_spec n).2
  have h1 := (sol_spec (n + 1)).2
  simp only [b]; omega

/-- k is in the set exactly when (2k+1)^2 + 23 = 8 y^2 for some y. -/
lemma S_iff (k : ℕ) : S k ↔ ∃ y, (2 * k + 1) ^ 2 + 23 = 8 * y ^ 2 := by
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
  have hsq : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
  unfold S
  rw [hsq, hj]
  constructor <;> rintro ⟨m, hm⟩ <;> exact ⟨m, by omega⟩

lemma range_b : Set.range b = {k | S k} := by
  ext k
  simp only [Set.mem_range, Set.mem_ofPred_eq, S_iff]
  constructor
  · rintro ⟨n, rfl⟩
    obtain ⟨h1, h2⟩ := sol_spec n
    refine ⟨(sol n).2, ?_⟩
    have : 2 * b n + 1 = (sol n).1 := by simp only [b]; omega
    rw [this]; exact h1
  · rintro ⟨y, hy⟩
    obtain ⟨n, hn⟩ := sol_complete y _ hy
    refine ⟨n, ?_⟩
    simp only [b, hn]; omega

/-- Seidov's form, for the listing indexed from 0. -/
lemma b_rec (n : ℕ) : (b (n + 4) : ℤ) = 6 * b (n + 2) - b n + 2 := by
  have e0 := (sol_spec n).2
  have e2 := (sol_spec (n + 2)).2
  have e4 := (sol_spec (n + 4)).2
  have s2 : sol (n + 2) = step (sol n) := rfl
  have s4 : sol (n + 4) = step (step (sol n)) := rfl
  have x2 : (sol (n + 2)).1 = 3 * (sol n).1 + 8 * (sol n).2 := by rw [s2]; rfl
  have x4 : (sol (n + 4)).1 = 17 * (sol n).1 + 48 * (sol n).2 := by
    rw [s4]; simp only [step]; ring
  have d0 : 2 * b n + 1 = (sol n).1 := by simp only [b]; omega
  have d2 : 2 * b (n + 2) + 1 = (sol (n + 2)).1 := by simp only [b]; omega
  have d4 : 2 * b (n + 4) + 1 = (sol (n + 4)).1 := by simp only [b]; omega
  omega

/-- The numerator and denominator of the conjectured generating function. -/
noncomputable def num : ℤ⟦X⟧ := X * (1 + 2 * X + 3 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4)
noncomputable def den : ℤ⟦X⟧ := (1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)

/-- **Mathar's conjectures, proved.** If `a` lists {k : 3 + k(k+1)/2 is a square} in
increasing order from index 1, then `a` has the conjectured initial terms, satisfies
Seidov's and Mathar's recurrences, and its generating function A(x) = Σ_{n ≥ 1} a(n) x^n
satisfies den · A = num, which is the conjectured g.f. (den has constant term 1, so it is
invertible and A = num / den). -/
theorem mathar (a : ℕ → ℕ) (hmono : ∀ n, 1 ≤ n → a n < a (n + 1))
    (hset : ∀ k, (∃ m, 3 + k * (k + 1) / 2 = m ^ 2) ↔ ∃ n, 1 ≤ n ∧ a n = k) :
    (a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 12 ∧ a 4 = 22) ∧
    (∀ n, 5 ≤ n → (a n : ℤ) = 6 * a (n - 2) - a (n - 4) + 2) ∧
    (∀ n, 6 ≤ n → (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    den * PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) = num := by
  -- a, shifted to start at 0, is the listing b.
  have hab : (fun n => a (n + 1)) = b := by
    have hm : StrictMono (fun n => a (n + 1)) :=
      strictMono_nat_of_lt_succ (fun n => hmono (n + 1) (by omega))
    refine (hm.range_inj_of_wellFoundedLT b_strictMono).1 ?_
    rw [range_b]
    ext k
    simp only [Set.mem_range, Set.mem_ofPred_eq, S, hset]
    constructor
    · rintro ⟨n, rfl⟩; exact ⟨n + 1, by omega, rfl⟩
    · rintro ⟨n, hn, rfl⟩; exact ⟨n - 1, by rw [Nat.sub_add_cancel hn]⟩
  have ha : ∀ n, a (n + 1) = b n := fun n => congrFun hab n
  have init : a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 12 ∧ a 4 = 22 ∧ a 5 = 73 := by
    refine ⟨ha 0, ha 1, ha 2, ha 3, ha 4⟩
  have seidov : ∀ n, 5 ≤ n → (a n : ℤ) = 6 * a (n - 2) - a (n - 4) + 2 := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have e1 : m + 5 - 2 = (m + 2) + 1 := by omega
    have e2 : m + 5 - 4 = m + 1 := by omega
    rw [e1, e2, show m + 5 = (m + 4) + 1 from rfl, ha, ha, ha]
    exact b_rec m
  have five : ∀ n, 6 ≤ n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5) := by
    intro n hn
    have h1 := seidov n (by omega)
    have h2 := seidov (n - 1) (by omega)
    have e1 : n - 1 - 2 = n - 3 := by omega
    have e2 : n - 1 - 4 = n - 5 := by omega
    rw [e1, e2] at h2
    linarith
  refine ⟨⟨init.1, init.2.1, init.2.2.1, init.2.2.2.1⟩, seidov, five, ?_⟩
  -- The generating function: compare coefficients.
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have hden : den = 1 - X - 6 * X ^ 2 + 6 * X ^ 3 + X ^ 4 - X ^ 5 := by
    simp only [den]; ring
  have hnum : num = X ^ 1 + C (2 : ℤ) * X ^ 2 + C (3 : ℤ) * X ^ 3 - C (2 : ℤ) * X ^ 4
      - C (2 : ℤ) * X ^ 5 := by
    simp only [num, map_ofNat, pow_one]; ring
  have hexp : den * A = A - X ^ 1 * A - C (6 : ℤ) * (X ^ 2 * A) + C (6 : ℤ) * (X ^ 3 * A)
      + X ^ 4 * A - X ^ 5 * A := by
    rw [hden, map_ofNat]; ring
  rw [hexp, hnum]
  ext n
  have cX : ∀ d : ℕ, coeff n (X ^ d : ℤ⟦X⟧) = if n = d then 1 else 0 := fun d => coeff_X_pow n d
  simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow_mul', hA, coeff_mk, cX]
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> simp [init.1, init.2.1, init.2.2.1, init.2.2.2.1, init.2.2.2.2]
  · have := five n hn
    simp only [show ¬ n = 0 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega,
      show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega,
      show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
      show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
      ite_true, ite_false]
    linarith

/-- A concrete listing satisfying the hypotheses of `mathar`, so they are not contradictory. -/
def listing (n : ℕ) : ℕ := b (n - 1)

theorem listing_spec :
    (∀ n, 1 ≤ n → listing n < listing (n + 1)) ∧
    (∀ k, (∃ m, 3 + k * (k + 1) / 2 = m ^ 2) ↔ ∃ n, 1 ≤ n ∧ listing n = k) := by
  refine ⟨fun n hn => ?_, fun k => ?_⟩
  · simp only [listing, show n + 1 - 1 = (n - 1) + 1 by omega]
    exact b_strictMono (Nat.lt_succ_self _)
  · have := congrArg (k ∈ ·) range_b
    simp only [Set.mem_range, Set.mem_ofPred_eq, S, eq_iff_iff] at this
    rw [← this]
    constructor
    · rintro ⟨n, rfl⟩; exact ⟨n + 1, by omega, rfl⟩
    · rintro ⟨n, -, rfl⟩; exact ⟨n - 1, rfl⟩

/-- The concrete listing starts as the entry's data does. -/
example : (List.range 12).map (fun i => listing (i + 1)) =
    [1, 3, 12, 22, 73, 131, 428, 766, 2497, 4467, 14556, 26038] := by decide

end A154138
