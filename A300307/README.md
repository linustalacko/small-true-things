# A300307: signed triangular numbers divisible by a power of 2

**Status: proved, and checked by Lean** (`SmallTrueThings/A300307.lean`, theorem `A300307.manyama`). November 28 2026.

## The conjecture

[A300307](https://oeis.org/A300307) counts the ways to choose signs in

  1 ± 3 ± 6 ± 10 ± … ± n(n+1)/2

so that the result is divisible by n. The first term always has a plus sign. For n = 7 there are 12 ways; the entry
lists them, one of which is 1 + 3 − 6 + 10 − 15 − 21 + 28 = 0. The sequence begins 1, 2, 0, 4, 4, 16, 12, 32, 20,
112, …

Seiichi Manyama, who made the entry in March 2018, gave one formula and marked it as conjectured:

> a(2^n) = 2^A000325(n) for n>0 (conjectured).

A000325(n) = 2^n − n. So for n = 2^m there are 2^(n−m) good sign choices. That is twice what a fair coin would
give: there are 2^(n−1) choices in all, and if the sums were spread evenly over the n residues, 2^(n−1)/n = 2^(n−1−m)
of them would land on 0. It is true for every m ≥ 1. (At m = 0 it fails, as the entry's "n>0" says: a(1) = 1.)

## The proof

Write T(k) = k(k+1)/2 and n = 2^m with m ≥ 1. A choice of signs is the set S ⊆ {2, …, n} of terms with a minus.

**Step 1: the total.** The sum with every sign plus is X = 1 + 3 + … + T(n) = n(n+1)(n+2)/6, and the signed sum is
X − 2·Σ_{k∈S} T(k). For n = 2^m,

  3X = 2^m · (2^m + 1) · (2^(m−1) + 1),

so 2^m divides X. Hence n divides the signed sum exactly when 2^m divides 2·Σ_S T(k), that is, when

  2^(m−1) divides Σ_{k∈S} T(k).

This is where the factor 2 over the fair-coin count comes from: the condition is modulo 2^(m−1), not 2^m.

**Step 2: one number of each 2-adic valuation.** T(2^(j+1)) = 2^j · (2^(j+1) + 1), and 2^(j+1) + 1 is odd. For
j = 0, …, m − 2 the index 2^(j+1) lies in {2, …, n}. So among the numbers T(2), …, T(n) there is, for each j < m − 1,
one that is 2^j times an odd number.

**Step 3: such a list has uniform subset sums.** *Lemma.* Let L be a finite list of integers that contains, for each
j < M, an element of the form 2^j · (odd). Then for every r, exactly 2^(|L| − M) subsets of L have sum ≡ r (mod 2^M).

By induction on M; M = 0 is the count of all subsets. For M + 1, take the element y = 2^M · (odd) and let L' be the
rest. A subset of L is a subset S of L', with or without y, and its sum is d = ΣS or d + y. Now y ≡ 2^M (mod 2^(M+1)).
If 2^M divides d − r, then exactly one of d − r and d + y − r is divisible by 2^(M+1); if not, neither is. So the
count for L modulo 2^(M+1) is the count for L' modulo 2^M, which is 2^(|L'| − M) = 2^(|L| − (M+1)) by induction,
because L' still holds the elements for j < M (they differ from y, having a different valuation).

**Step 4.** Apply the lemma to T(2), …, T(n), a list of n − 1 numbers, with M = m − 1 and r = 0. The count is
2^((n−1) − (m−1)) = 2^(n−m) = 2^A000325(m). ∎

The idea in one line: the triangular numbers up to 2^m contain one number of each 2-adic valuation below m − 1,
which makes their signed sums equidistributed modulo 2^(m−1), and the total is divisible by 2^m.

The same argument gives the formula a(2^n) = 2^A000325(n), n > 1, printed without proof on the sibling
[A300190](https://oeis.org/A300190) (1 ± 2 ± … ± n): there the numbers 2^j, 1 ≤ j < m − 1, and 3 give the valuations,
and the total n(n+1)/2 is divisible by 2^(m−1) only, so the condition is a congruence modulo 2^(m−1) to a fixed
residue, which the lemma counts the same way. That remark is not checked by Lean.

## What was checked, and how

| Check | Result |
|---|---|
| `python3 A300307/check.py` | The count by dynamic programming over residues agrees with the 19 terms printed on the entry; a(2^m) = 2^(2^m − m) for m = 1..13, so n up to 8192 (the entry's b-file has the terms the author computed); the lemma holds on 300 random lists |
| `lake build` | `A300307.manyama` compiles; `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` for it, for `A300307.count_two_pow` and for `A300307.uniform` |

The Lean theorem takes any `a : ℕ → ℕ` such that, for n ≥ 1, `a n` is the number of sets S ⊆ {2, …, n} with
n ∣ 1 + Σ_{k=2..n} (if k ∈ S then −1 else 1)·T(k), where T(k) = k(k+1)/2 with natural-number division, as the entry
defines its terms. It concludes a(2^m) = 2^(2^m − m) for every m ≥ 1. `A300307.count` is the count itself, so the
hypothesis describes a real sequence; a `decide` check in the file confirms its first six values against the entry,
and `A300307.count_two_pow` is the theorem for it. `A300307.uniform` is the lemma of Step 3, for any weights.

What Lean does not check: that "solutions to 1 ± 3 ± … ± n(n+1)/2 ≡ 0 mod n" means sign choices with the first sign
fixed. The entry's example for n = 7 and its first terms (1, 2, 0, 4, … matched by `check.py` and, for six terms, by
Lean) say it does.

## Novelty checks

Run on November 28 2026, before the proof was started:

1. The entry (read on the GitHub mirror oeis/oeisdata, November 28) has no proof and no comment about the formula.
   Its links are a b-file. Its cross-references A000079, A000217, A000325, A058498, A300190, A300218 and the triangle
   A300324 have no proof of it; A300190 prints the analogous formula for 1 ± 2 ± … ± n without a proof or a
   reference.
2. It is not a corollary of a formula on the entry or its cross-references: none of them gives the distribution of
   the signed sums.
3. Web searches for the entry number with the formula, and for the problem in words, found nothing about it.
4. The trureturing project (the-omega-institute/trureturing) and the open-math-agents project
   (GuillaumeBAUD-coder/open-math-agents) have no issue, pull request or file mentioning A300307 (searched with
   `gh api search/issues` and `gh search code`).

So no earlier proof was found. That is not a claim to be first. The lemma in Step 3 is a standard fact about subset
sums, and a specialist would find the proof routine.

## Not done

Nothing has been sent to the OEIS. A comment for the entry, if Linus wants to send one:

> The conjectured formula is true. Write T(k) = k(k+1)/2 and n = 2^m, m >= 1. The sum with all signs + is
> n(n+1)(n+2)/6, which is divisible by 2^m, so a sign choice works iff the sum of T(k) over the minus terms is
> divisible by 2^(m-1). The terms T(2^(j+1)) = 2^j*(2^(j+1)+1), j = 0..m-2, have every 2-adic valuation below m-1,
> and that makes the n-1 subset sums of T(2..n) uniformly distributed mod 2^(m-1) (remove the term of valuation
> M-1 and induct on M). Hence a(2^m) = 2^(n-1)/2^(m-1) = 2^(2^m-m). The same argument proves the formula on A300190.
> The proof was found by an AI (Claude) and is formalized in Lean 4.
