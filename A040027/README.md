# A040027: the Gould numbers from the alternating factorials

**Status: proved, and checked by Lean** (`SmallTrueThings/A040027.lean`, theorem `A040027.yanev`). November 20 2026.

## The conjecture

[A040027](https://oeis.org/A040027) is 1, 1, 3, 9, 31, 121, 523, 2469, …, the Gould numbers: a(n) is the number of
set partitions of {1, …, n+1} whose last block, with blocks in order of their least element, is a single element.
The entry gives them by the recurrence (Jon Perry, 2005)

> a(0) = 1, a(1) = 1, a(n) = n + Σ_{j=1..n-1} C(n, j+1) · a(j) for n > 1,

which is the same as a(n) = Σ_{i=0..n-1} C(n, i+1) · a(i) for n ≥ 1 (Jovovic, 2001), since the i = 0 term is n.

The entry carries this comment by Velin Yanev, dated August 31 2021:

> Conjecture: a(n) = Sum_{k = 0..n} A058006(k)*A048993(n+1, k+1)

Here A048993(n,k) = S(n,k) is the Stirling number of the second kind, and A058006(k) = 0! − 1! + 2! − … + (−1)^k k!
is the alternating factorial: 1, 0, 2, −4, 20, −100, 620, …. Write c(k) for it. So the claim is that a sequence of
positive counts is a signed combination of Stirling numbers:

> a(n) = Σ_{k=0..n} c(k) · S(n+1, k+1).

## The proof

Two identities for Stirling numbers of the second kind.

1. **Remove the block of the last element.** S(n+1, m+1) = Σ_{j=0..n} C(n,j) · S(j,m): if that block has n − j
   other elements, the j left over form m blocks.
2. **An alternating sum.** Σ_{k=0..n} (−1)^k k! · S(n+1, k+1) is 1 for n = 0 and 0 for n ≥ 1. (Put
   S(n+2, k+1) = (k+1) · S(n+1, k+1) + S(n+1, k) into the sum for n+1; the two halves cancel term by term.)

**Theorem.** g(n) = Σ_{k=0..n} c(k) · S(n+1, k+1) equals a(n) for all n ≥ 0.

*Proof.* g(0) = c(0) · S(1,1) = 1. For n ≥ 1, put g into the right side of the recurrence, swap the sums and use
identity 1 with m = k+1:

> Σ_{i=0..n-1} C(n, i+1) · g(i) = Σ_k c(k) · Σ_{i} C(n, i+1) · S(i+1, k+1) = Σ_{k=0..n-1} c(k) · S(n+1, k+2).

On the other side, shift the index and use c(k+1) = c(k) + (−1)^{k+1} (k+1)!:

> g(n) = c(0) · S(n+1, 1) + Σ_{k=0..n-1} c(k+1) · S(n+1, k+2)
> = Σ_{k=0..n-1} c(k) · S(n+1, k+2) + Σ_{k=0..n} (−1)^k k! · S(n+1, k+1).

The last sum is 0 by identity 2. So g obeys the recurrence of a, with the same start. ∎

## Why the alternating factorials

The proof never uses what c is until the last line. For any sequence c with differences d(k) = c(k) − c(k−1),

> g(n) − Σ_{i<n} C(n, i+1) · g(i) = Σ_k d(k) · S(n+1, k+1).

The Gould recurrence asks for the right side to be 1 at n = 0 and 0 after. The matrix S(n+1, k+1) is triangular
with ones on the diagonal, so exactly one d does that: the first column of its inverse, d(k) = (−1)^k k!, which is
the Stirling number of the first kind s(k+1, 1). So the alternating factorials are forced, and the conjecture is
the orthogonality of the two kinds of Stirling numbers, summed once.

## What was checked, and how

| Check | Result |
|---|---|
| `python3 A040027/check.py 300 9` | The conjecture holds for n ≤ 300; the first 23 terms match the OEIS; the recurrence counts the partitions with a singleton last block for n ≤ 9, by listing them; both identities hold for n < 60 |
| `lake build` | `A040027.yanev` compiles; `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` |

The Lean theorem takes any `a : ℕ → ℕ` and assumes exactly Perry's recurrence, with `Nat.stirlingSecond` from
Mathlib; `altFactorial` is the alternating factorial written as its sum. `gould` in the same file obeys the
recurrence, which shows the hypotheses do not contradict each other.

What Lean does not check: that the recurrence counts those partitions (the entry's own claim; brute force agrees
for n ≤ 9). The section "Why the alternating factorials" is on paper only.

## Not done

Nothing has been sent to the OEIS, and I did not search the literature for an earlier proof; the entry showed none
on November 20 2026. A comment for the entry, if Linus wants to send one:

> Yanev's conjecture is true. Let g(n) be the right side and c = A058006. By
> Stirling2(n+1,m+1) = Sum_{j=0..n} binomial(n,j)*Stirling2(j,m),
> g(n) - Sum_{i=0..n-1} binomial(n,i+1)*g(i) = Sum_{k=0..n} (c(k)-c(k-1))*Stirling2(n+1,k+1)
> = Sum_{k=0..n} (-1)^k*k!*Stirling2(n+1,k+1) = 0 for n >= 1, so g satisfies the recurrence of a. The proof was
> found by an AI (Claude) and is formalized in Lean 4.
