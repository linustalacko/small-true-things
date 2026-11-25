/-
A154145: the numbers k for which 15 plus the k-th triangular number is a square.

The OEIS entry A154145 (1, 4, 6, 11, 20, 33, 43, 70, 121, ..., offset 1) is defined as
  {k: 15+k*(k+1)/2 in A000290}
and carries these formulas, marked as conjectures (R. J. Mathar, Oct 18 2009):

  a(n)= +a(n-1) +6*a(n-4) -6*a(n-5) -a(n-8) +a(n-9);
  G.f.: x*(-1-3*x-2*x^2-5*x^3-3*x^4+5*x^5+2*x^6+3*x^7+2*x^8)/((x-1) * (x^4+2*x^2-1) * (x^4-2*x^2-1)).

It also carries a comment (Ctibor O. Zizka, Nov 13 2009): a(1..4)=(1,4,6,11);
a(n>4)=6*a(n-2)-a(n-4)+2. That form is the one true for the siblings A154138 to A154144,
and it is false here: a(5) = 20, while 6*a(3) - a(1) + 2 = 37.

`A154145.mathar` proves Mathar's two conjectures, the four-chain form
a(n) = 6a(n-4) - a(n-8) + 2 behind them, and the failure of Zizka's form, for any `a` that
lists the set in increasing order from index 1. `A154145.listing` is such an `a`.

The idea. With x = 2k+1, 15 + k(k+1)/2 = y^2 says x^2 + 119 = 8y^2. The map
(x, y) ↦ (3x - 8y, 3y - x) sends a solution with y ≥ 12 to one with a smaller y, so every
solution climbs by (x, y) ↦ (3x + 8y, x + 3y) from one of (3, 4), (9, 5), (13, 6), (23, 9).
Taken in turn, the four chains are already in increasing order.
-/
import Mathlib

open PowerSeries

namespace A154145

/-- The set of the entry: 15 plus the k-th triangular number is a square. -/
def S (k : ℕ) : Prop := ∃ m, 15 + k * (k + 1) / 2 = m ^ 2

/-- Multiplication by the unit 3 + √8. -/
def step (p : ℕ × ℕ) : ℕ × ℕ := (3 * p.1 + 8 * p.2, p.1 + 3 * p.2)

/-- The solutions of x^2 + 119 = 8y^2 in increasing order: four chains, interleaved. -/
def sol : ℕ → ℕ × ℕ
  | 0 => (3, 4)
  | 1 => (9, 5)
  | 2 => (13, 6)
  | 3 => (23, 9)
  | n + 4 => step (sol n)

/-- The listing: k = (x - 1)/2, indexed from 0. -/
def b (n : ℕ) : ℕ := ((sol n).1 - 1) / 2

lemma step_eq {x y : ℕ} (h : x ^ 2 + 119 = 8 * y ^ 2) :
    (step (x, y)).1 ^ 2 + 119 = 8 * (step (x, y)).2 ^ 2 := by
  simp only [step]
  nlinarith [h]

/-- Every term is a solution, and its x is odd. -/
lemma sol_spec (n : ℕ) : (sol n).1 ^ 2 + 119 = 8 * (sol n).2 ^ 2 ∧ (sol n).1 % 2 = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
    | n + 4, ih =>
      obtain ⟨h1, h2⟩ := ih n (by omega)
      have hp : sol n = ((sol n).1, (sol n).2) := rfl
      refine ⟨?_, ?_⟩
      · show (step (sol n)).1 ^ 2 + 119 = 8 * (step (sol n)).2 ^ 2
        rw [hp]; exact step_eq h1
      · show (3 * (sol n).1 + 8 * (sol n).2) % 2 = 1
        omega

/-- The descent: every solution is a term. -/
lemma sol_complete : ∀ y x : ℕ, x ^ 2 + 119 = 8 * y ^ 2 → ∃ n, sol n = (x, y) := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro x h
    by_cases hy : y ≤ 11
    · have hx : x ≤ 29 := by nlinarith
      interval_cases y <;> interval_cases x <;> simp_all
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
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
      have h' : x' ^ 2 + 119 = 8 * y' ^ 2 := by
        subst ex ey; nlinarith [h]
      obtain ⟨n, hn⟩ := ih y' (by omega) x' h'
      refine ⟨n + 4, ?_⟩
      show step (sol n) = (x, y)
      rw [hn, ex, ey]; rfl

/-- Componentwise order on pairs. -/
def lt (p q : ℕ × ℕ) : Prop := p.1 < q.1 ∧ p.2 < q.2

/-- Four consecutive terms increase, and the fourth lies below the image of the first. -/
lemma sol_order (n : ℕ) :
    lt (sol n) (sol (n + 1)) ∧ lt (sol (n + 1)) (sol (n + 2)) ∧
    lt (sol (n + 2)) (sol (n + 3)) ∧ lt (sol (n + 3)) (step (sol n)) := by
  induction n with
  | zero => simp only [lt]; decide
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    refine ⟨h2, h3, h4, ?_⟩
    obtain ⟨a1, a2⟩ := h1
    show lt (step (sol n)) (step (sol (n + 1)))
    simp only [lt, step]; constructor <;> omega

lemma b_strictMono : StrictMono b := by
  apply strictMono_nat_of_lt_succ
  intro n
  have := (sol_order n).1.1
  have h0 := (sol_spec n).2
  have h1 := (sol_spec (n + 1)).2
  simp only [b]; omega

/-- k is in the set exactly when (2k+1)^2 + 119 = 8 y^2 for some y. -/
lemma S_iff (k : ℕ) : S k ↔ ∃ y, (2 * k + 1) ^ 2 + 119 = 8 * y ^ 2 := by
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

/-- The four-chain form, for the listing indexed from 0. -/
lemma b_rec (n : ℕ) : (b (n + 8) : ℤ) = 6 * b (n + 4) - b n + 2 := by
  have e0 := (sol_spec n).2
  have e4 := (sol_spec (n + 4)).2
  have e8 := (sol_spec (n + 8)).2
  have s4 : sol (n + 4) = step (sol n) := rfl
  have s8 : sol (n + 8) = step (step (sol n)) := rfl
  have x4 : (sol (n + 4)).1 = 3 * (sol n).1 + 8 * (sol n).2 := by rw [s4]; rfl
  have x8 : (sol (n + 8)).1 = 17 * (sol n).1 + 48 * (sol n).2 := by
    rw [s8]; simp only [step]; ring
  have d0 : 2 * b n + 1 = (sol n).1 := by simp only [b]; omega
  have d4 : 2 * b (n + 4) + 1 = (sol (n + 4)).1 := by simp only [b]; omega
  have d8 : 2 * b (n + 8) + 1 = (sol (n + 8)).1 := by simp only [b]; omega
  omega

/-- The numerator and denominator of the conjectured generating function, as printed. -/
noncomputable def num : ℤ⟦X⟧ :=
  X * (-1 - 3 * X - 2 * X ^ 2 - 5 * X ^ 3 - 3 * X ^ 4 + 5 * X ^ 5 + 2 * X ^ 6 + 3 * X ^ 7
    + 2 * X ^ 8)
noncomputable def den : ℤ⟦X⟧ := (X - 1) * (X ^ 4 + 2 * X ^ 2 - 1) * (X ^ 4 - 2 * X ^ 2 - 1)

/-- **Mathar's conjectures, proved, and Zizka's form refuted.** If `a` lists
{k : 15 + k(k+1)/2 is a square} in increasing order from index 1, then `a` starts
1, 4, 6, 11, 20, 33, 43, 70, 121, satisfies a(n) = 6a(n-4) - a(n-8) + 2 for n ≥ 9 and
Mathar's recurrence for n ≥ 10, and its generating function A(x) = Σ_{n ≥ 1} a(n) x^n
satisfies den · A = num (den has constant term -1, so it is invertible and A = num / den).
Zizka's a(n) = 6a(n-2) - a(n-4) + 2 for n > 4 does not hold. -/
theorem mathar (a : ℕ → ℕ) (hmono : ∀ n, 1 ≤ n → a n < a (n + 1))
    (hset : ∀ k, (∃ m, 15 + k * (k + 1) / 2 = m ^ 2) ↔ ∃ n, 1 ≤ n ∧ a n = k) :
    (a 1 = 1 ∧ a 2 = 4 ∧ a 3 = 6 ∧ a 4 = 11 ∧ a 5 = 20 ∧ a 6 = 33 ∧ a 7 = 43 ∧ a 8 = 70 ∧
      a 9 = 121) ∧
    (∀ n, 9 ≤ n → (a n : ℤ) = 6 * a (n - 4) - a (n - 8) + 2) ∧
    (∀ n, 10 ≤ n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 4) - 6 * a (n - 5) - a (n - 8) + a (n - 9)) ∧
    den * PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) = num ∧
    ¬ (∀ n, 5 ≤ n → (a n : ℤ) = 6 * a (n - 2) - a (n - 4) + 2) := by
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
  have init : a 1 = 1 ∧ a 2 = 4 ∧ a 3 = 6 ∧ a 4 = 11 ∧ a 5 = 20 ∧ a 6 = 33 ∧ a 7 = 43 ∧
      a 8 = 70 ∧ a 9 = 121 := by
    refine ⟨ha 0, ha 1, ha 2, ha 3, ha 4, ha 5, ha 6, ha 7, ha 8⟩
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ := init
  have four : ∀ n, 9 ≤ n → (a n : ℤ) = 6 * a (n - 4) - a (n - 8) + 2 := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    have e1 : m + 9 - 4 = (m + 4) + 1 := by omega
    have e2 : m + 9 - 8 = m + 1 := by omega
    rw [e1, e2, show m + 9 = (m + 8) + 1 from rfl, ha, ha, ha]
    exact b_rec m
  have nine : ∀ n, 10 ≤ n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 4) - 6 * a (n - 5) - a (n - 8) + a (n - 9) := by
    intro n hn
    have h1 := four n (by omega)
    have h2 := four (n - 1) (by omega)
    have e1 : n - 1 - 4 = n - 5 := by omega
    have e2 : n - 1 - 8 = n - 9 := by omega
    rw [e1, e2] at h2
    linarith
  refine ⟨⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩, four, nine, ?_, ?_⟩
  · -- The generating function: compare coefficients.
    set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
    have hden : den = -1 + X + 6 * X ^ 4 - 6 * X ^ 5 - X ^ 8 + X ^ 9 := by
      simp only [den]; ring
    have hnum : num = - X ^ 1 - C (3 : ℤ) * X ^ 2 - C (2 : ℤ) * X ^ 3 - C (5 : ℤ) * X ^ 4
        - C (3 : ℤ) * X ^ 5 + C (5 : ℤ) * X ^ 6 + C (2 : ℤ) * X ^ 7 + C (3 : ℤ) * X ^ 8
        + C (2 : ℤ) * X ^ 9 := by
      simp only [num, map_ofNat, pow_one]; ring
    have hexp : den * A = - A + X ^ 1 * A + C (6 : ℤ) * (X ^ 4 * A) - C (6 : ℤ) * (X ^ 5 * A)
        - X ^ 8 * A + X ^ 9 * A := by
      rw [hden, map_ofNat]; ring
    rw [hexp, hnum]
    ext n
    have cX : ∀ d : ℕ, coeff n (X ^ d : ℤ⟦X⟧) = if n = d then 1 else 0 :=
      fun d => coeff_X_pow n d
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_X_pow_mul', hA, coeff_mk, cX]
    rcases Nat.lt_or_ge n 10 with hn | hn
    · interval_cases n <;> simp [i1, i2, i3, i4, i5, i6, i7, i8, i9]
    · have := nine n hn
      simp only [show ¬ n = 0 by omega, show 1 ≤ n by omega, show 4 ≤ n by omega,
        show 5 ≤ n by omega, show 8 ≤ n by omega, show 9 ≤ n by omega,
        show n - 1 ≠ 0 by omega, show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega,
        show n - 8 ≠ 0 by omega, show n - 9 ≠ 0 by omega, show n ≠ 1 by omega,
        show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
        show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega, show n ≠ 9 by omega,
        ite_true, ite_false]
      linarith
  · -- Zizka's form fails at n = 5: 20 against 6 * 6 - 1 + 2 = 37.
    intro h
    have := h 5 (le_refl 5)
    norm_num [i5, i3, i1] at this

/-- A concrete listing satisfying the hypotheses of `mathar`, so they are not contradictory. -/
def listing (n : ℕ) : ℕ := b (n - 1)

theorem listing_spec :
    (∀ n, 1 ≤ n → listing n < listing (n + 1)) ∧
    (∀ k, (∃ m, 15 + k * (k + 1) / 2 = m ^ 2) ↔ ∃ n, 1 ≤ n ∧ listing n = k) := by
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
example : (List.range 16).map (fun i => listing (i + 1)) =
    [1, 4, 6, 11, 20, 33, 43, 70, 121, 196, 254, 411, 708, 1145, 1483, 2398] := by decide

end A154145
