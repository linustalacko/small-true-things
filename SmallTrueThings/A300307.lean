/-
A300307: signed sums of triangular numbers divisible by a power of 2.

The OEIS entry A300307 (Seiichi Manyama, 2018) is

  Number of solutions to 1 +- 3 +- 6 +- ... +- n*(n+1)/2 == 0 mod n.

and carries the formula

  a(2^n) = 2^A000325(n) for n>0 (conjectured).

where A000325(n) = 2^n - n. The first sign is +; each later term T(k) = k(k+1)/2, k = 2..n,
gets a sign. A choice of signs is the set `S ⊆ {2, ..., n}` of terms that get a minus.

`A300307.manyama` proves the conjecture for any `a` that counts exactly these sign choices.
`A300307.count` is that count, so the hypothesis describes a real sequence, and
`A300307.count_two_pow` is the statement for it.

The idea: the signed sum is X - 2 * (sum of T over S), where X = 1 + 3 + ... + T(n).
For n = 2^m, 2^m divides X, so the condition is that 2^(m-1) divides the sum of T over S.
The numbers T(2^(j+1)) = 2^j * (2^(j+1) + 1), j < m - 1, have every 2-adic valuation below
m - 1, and that alone makes the subset sums uniform modulo 2^(m-1) (`uniform`).
-/
import Mathlib.Tactic

open Finset

namespace A300307

/-- The triangular number `T k = k(k+1)/2`. -/
def T (k : ℕ) : ℕ := k * (k + 1) / 2

/-! ### Subset sums are uniform modulo `2^M` -/

/-- One term `y` with weight `2^M` times an odd number: the subsets with and without it
together hit a class modulo `2^(M+1)` exactly when the rest hits it modulo `2^M`. -/
lemma split (M : ℕ) (q d : ℤ) :
    ((if (2 : ℤ) ^ (M + 1) ∣ d then 1 else 0) +
      (if (2 : ℤ) ^ (M + 1) ∣ 2 ^ M * (2 * q + 1) + d then 1 else 0) : ℕ) =
      if (2 : ℤ) ^ M ∣ d then 1 else 0 := by
  have hP : (2 : ℤ) ^ M ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [pow_succ]
  by_cases hd : (2 : ℤ) ^ M ∣ d
  · obtain ⟨t, rfl⟩ := hd
    have e1 : (2 : ℤ) ^ M * 2 ∣ 2 ^ M * t ↔ t % 2 = 0 := by
      rw [mul_dvd_mul_iff_left hP, Int.dvd_iff_emod_eq_zero]
    have e2 : (2 : ℤ) ^ M * 2 ∣ 2 ^ M * (2 * q + 1) + 2 ^ M * t ↔ (2 * q + 1 + t) % 2 = 0 := by
      rw [← mul_add, mul_dvd_mul_iff_left hP, Int.dvd_iff_emod_eq_zero]
    have e3 : (2 : ℤ) ^ M ∣ 2 ^ M * t := dvd_mul_right _ _
    simp only [e1, e2, e3, ite_true]
    split_ifs <;> omega
  · have h1 : ¬ (2 : ℤ) ^ M * 2 ∣ d := fun h => hd (dvd_trans (dvd_mul_right _ _) h)
    have h2 : ¬ (2 : ℤ) ^ M * 2 ∣ 2 ^ M * (2 * q + 1) + d := by
      intro h
      exact hd ((dvd_add_right (dvd_mul_right _ _)).mp (dvd_trans (dvd_mul_right _ _) h))
    simp [h1, h2, hd]

/-- If `s` holds, for each `j < M`, an index whose weight is `2^j` times an odd number,
then the subsets of `s` are spread evenly over the classes modulo `2^M`. -/
theorem uniform (w : ℕ → ℤ) :
    ∀ (M : ℕ) (s : Finset ℕ) (r : ℤ),
      (∀ j < M, ∃ i ∈ s, ∃ q : ℤ, w i = 2 ^ j * (2 * q + 1)) →
      (∑ S ∈ s.powerset, if (2 : ℤ) ^ M ∣ (∑ k ∈ S, w k) - r then 1 else 0) =
        2 ^ (s.card - M) := by
  intro M
  induction M with
  | zero =>
    intro s r _
    simp [card_powerset]
  | succ M ih =>
    intro s r h
    obtain ⟨y, hy, q, hq⟩ := h M (Nat.lt_succ_self M)
    have hrest : ∀ j < M, ∃ i ∈ s.erase y, ∃ q : ℤ, w i = 2 ^ j * (2 * q + 1) := by
      intro j hj
      obtain ⟨i, hi, q', hq'⟩ := h j (by omega)
      refine ⟨i, mem_erase.mpr ⟨?_, hi⟩, q', hq'⟩
      rintro rfl
      have hpow : (2 : ℤ) ^ M = 2 ^ j * (2 * 2 ^ (M - j - 1)) := by
        have hM : M = j + 1 + (M - j - 1) := by omega
        calc (2 : ℤ) ^ M = 2 ^ (j + 1 + (M - j - 1)) := by rw [← hM]
          _ = _ := by ring
      rw [hq, hpow, mul_assoc] at hq'
      have := mul_left_cancel₀ (pow_ne_zero j (two_ne_zero : (2 : ℤ) ≠ 0)) hq'
      rw [mul_assoc] at this
      omega
    have hy' : y ∉ s.erase y := notMem_erase y s
    rw [← insert_erase hy, sum_powerset_insert hy']
    have hsecond : ∀ S ∈ (s.erase y).powerset,
        (if (2 : ℤ) ^ (M + 1) ∣ (∑ k ∈ insert y S, w k) - r then 1 else 0 : ℕ) =
          if (2 : ℤ) ^ (M + 1) ∣ 2 ^ M * (2 * q + 1) + ((∑ k ∈ S, w k) - r) then 1 else 0 := by
      intro S hS
      have hyS : y ∉ S := fun h => hy' (mem_powerset.mp hS h)
      rw [sum_insert hyS, hq]
      congr 2
      ring
    rw [sum_congr rfl hsecond, ← sum_add_distrib]
    simp only [split]
    rw [ih (s.erase y) r hrest, card_insert_of_notMem hy', card_erase_of_mem hy]
    congr 1
    have := card_pos.mpr ⟨y, hy⟩
    omega

/-! ### The triangular numbers -/

lemma T_two_mul (k : ℕ) : T k * 2 = k * (k + 1) := by
  unfold T
  exact Nat.div_mul_cancel (Nat.even_mul_succ_self k).two_dvd

/-- `T (2^(j+1)) = 2^j * (2^(j+1) + 1)`: weight `2^j` times an odd number. -/
lemma T_two_pow (j : ℕ) : (T (2 ^ (j + 1)) : ℤ) = 2 ^ j * (2 * 2 ^ j + 1) := by
  have h := T_two_mul (2 ^ (j + 1))
  have h' : (T (2 ^ (j + 1)) : ℤ) * 2 = 2 ^ (j + 1) * (2 ^ (j + 1) + 1) := by exact_mod_cast h
  have e : (2 : ℤ) ^ (j + 1) = 2 * 2 ^ j := pow_succ' 2 j
  rw [e] at h'
  linarith [h']

/-- `1 + 3 + 6 + ... + T(n) = n(n+1)(n+2)/6`, in the form six times it. -/
lemma six_mul_total (n : ℕ) (hn : 1 ≤ n) :
    6 * (1 + ∑ k ∈ Icc 2 n, T k) = n * (n + 1) * (n + 2) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [sum_Icc_succ_top (by omega), ← add_assoc, mul_add, ih]
    have := T_two_mul (n + 1)
    nlinarith [this]

/-- For `n = 2^m`, `m ≥ 1`, the total `1 + 3 + ... + T(n)` is divisible by `n`. -/
lemma two_pow_dvd_total (m : ℕ) (hm : 1 ≤ m) :
    2 ^ m ∣ 1 + ∑ k ∈ Icc 2 (2 ^ m), T k := by
  have h6 := six_mul_total (2 ^ m) Nat.one_le_two_pow
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h3 : 3 * (1 + ∑ k ∈ Icc 2 (2 ^ (m' + 1)), T k) =
      2 ^ (m' + 1) * ((2 ^ (m' + 1) + 1) * (2 ^ m' + 1)) := by
    rw [pow_succ] at h6 ⊢
    nlinarith [h6]
  have hcop : Nat.Coprime (2 ^ (m' + 1)) 3 := Nat.Coprime.pow_left _ (by norm_num)
  exact hcop.dvd_of_dvd_mul_left ⟨_, h3⟩

/-- Signs as a set of minus terms: the signed sum is the total minus twice the sum over `S`. -/
lemma signed_sum (n : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 2 n) :
    (1 : ℤ) + ∑ k ∈ Icc 2 n, (if k ∈ S then -1 else 1) * (T k : ℤ) =
      ((1 + ∑ k ∈ Icc 2 n, T k : ℕ) : ℤ) - 2 * ∑ k ∈ S, (T k : ℤ) := by
  have : ∀ k ∈ Icc 2 n, (if k ∈ S then -1 else 1) * (T k : ℤ) =
      (T k : ℤ) - 2 * (if k ∈ S then (T k : ℤ) else 0) := by
    intro k _; split_ifs <;> ring
  rw [sum_congr rfl this, sum_sub_distrib, ← mul_sum, sum_ite_mem, inter_eq_right.mpr hS]
  push_cast
  ring

/-! ### The conjecture -/

/-- Manyama's conjecture: if `a n` counts the sign choices with
`1 ± 3 ± 6 ± ... ± T(n) ≡ 0 (mod n)`, then `a(2^m) = 2^(2^m - m)` for `m ≥ 1`. -/
theorem manyama (a : ℕ → ℕ)
    (ha : ∀ n ≥ 1, a n = ((Icc 2 n).powerset.filter (fun S =>
      (n : ℤ) ∣ 1 + ∑ k ∈ Icc 2 n, (if k ∈ S then -1 else 1) * (T k : ℤ))).card) :
    ∀ m ≥ 1, a (2 ^ m) = 2 ^ (2 ^ m - m) := by
  intro m hm
  rw [ha _ Nat.one_le_two_pow, card_filter]
  obtain ⟨X, hX⟩ := two_pow_dvd_total m hm
  have hcond : ∀ S ∈ (Icc 2 (2 ^ m)).powerset,
      (if ((2 ^ m : ℕ) : ℤ) ∣ 1 + ∑ k ∈ Icc 2 (2 ^ m), (if k ∈ S then -1 else 1) * (T k : ℤ)
        then 1 else 0 : ℕ) =
      if (2 : ℤ) ^ (m - 1) ∣ (∑ k ∈ S, (T k : ℤ)) - 0 then 1 else 0 := by
    intro S hS
    rw [signed_sum _ S (mem_powerset.mp hS), hX, sub_zero]
    have h2 : ((2 ^ m : ℕ) : ℤ) = 2 ^ (m - 1) * 2 := by
      push_cast; rw [← pow_succ]; congr 1; omega
    have hiff : ((2 ^ m : ℕ) : ℤ) ∣ ((2 ^ m * X : ℕ) : ℤ) - 2 * ∑ k ∈ S, (T k : ℤ) ↔
        (2 : ℤ) ^ (m - 1) ∣ ∑ k ∈ S, (T k : ℤ) := by
      rw [← dvd_neg, neg_sub, Nat.cast_mul,
        dvd_sub_left (dvd_mul_right _ _), h2, mul_comm (2 : ℤ) _,
        mul_dvd_mul_iff_right two_ne_zero]
    simp only [hiff]
  rw [sum_congr rfl hcond]
  rw [uniform (fun k => (T k : ℤ)) (m - 1) (Icc 2 (2 ^ m)) 0]
  · rw [Nat.card_Icc]
    congr 1
    omega
  · intro j hj
    refine ⟨2 ^ (j + 1), mem_Icc.mpr ⟨?_, ?_⟩, 2 ^ j, T_two_pow j⟩
    · calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ### The hypothesis describes a real sequence -/

/-- The count itself. -/
def count (n : ℕ) : ℕ :=
  ((Icc 2 n).powerset.filter (fun S =>
    (n : ℤ) ∣ 1 + ∑ k ∈ Icc 2 n, (if k ∈ S then -1 else 1) * (T k : ℤ))).card

set_option maxRecDepth 100000 in
/-- The definition agrees with the entry's first terms. -/
example : (List.range 6).map (fun i => count (i + 1)) = [1, 2, 0, 4, 4, 16] := by
  decide

theorem count_two_pow : ∀ m ≥ 1, count (2 ^ m) = 2 ^ (2 ^ m - m) :=
  manyama count (fun _ _ => rfl)

end A300307
