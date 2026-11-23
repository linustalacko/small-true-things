# A056240: the cheapest number with a given sum of prime factors

**Status: proved, and checked by Lean** (`SmallTrueThings/A056240.lean`, theorem `A056240.sycamore_marcus`).
November 23 2026, after a first day (November 22) that proved the even case on paper.

## The conjecture

[A056240](https://oeis.org/A056240) is 2, 3, 4, 5, 8, 7, 15, 14, 21, 11, 35, …: a(n) is the smallest number whose
prime factors, counted with multiplicity, add up to n. So a(8) = 15 = 3 · 5, since 3 + 5 = 8 and nothing smaller
has prime factors adding to 8.

The entry carries this comment by David James Sycamore and Michel Marcus, June 2017:

> For even composite n, let P_n denote the largest prime < n-1 such that n-P_n is prime (except if n = 6).
> For odd composite n, let P_n denote the largest prime < n-1 such that n-3-P_n is prime.
> Conjecture: a(n) = min { q*a(n-q); q prime, P_n <= q < n-1 }.

In words: to find the cheapest number with prime-factor sum n, you only ever need to try a largest factor q from
P_n up. The entry's example: for n = 9998, P_n = 9967 and a(9998) = min{9973 · a(25), 9967 · a(31)} = 9967 · 31.

For even n, P_n exists exactly when n is a sum of two primes, so its existence is Goldbach's conjecture. The
conjecture is about the n where P_n exists, and the proof here assumes nothing more: it holds for every composite
n ≠ 6 that has a P_n. (For n = 6 the formula really fails: a(6) = 8 = 2 · 2 · 2, but the only q allowed is 3,
giving 3 · a(3) = 9.)

## The proof

Write B for the prime factors of a(n), with multiplicity; they add up to n and multiply to a(n).

**Step 1: any prime factor works.** If q is in B, then a(n)/q has prime factors adding to n − q, so
a(n − q) ≤ a(n)/q; and q · a(n − q) has prime factors adding to n, so a(n) ≤ q · a(n − q). Hence
a(n) = q · a(n − q), and q < n − 1 because n is composite. Every q in the range gives at least a(n), so the
conjecture says exactly: **some prime factor of a(n) is at least P = P_n.** Suppose not: every part of B is below P.

**Step 2: the product bound.** *If integers, each at least 2 and at most P, add up to P + r with r ≤ P and P ≥ 5,
their product is at least P · r.* Two easy facts carry it: integers at least 2 multiply to at least their sum, and
so a list split into groups multiplies to at least the product of the group sums.

- If some part x is at least r, split it from the rest: the product is at least x · (P + r − x), and
  x(P + r − x) − Pr = (P − x)(x − r) ≥ 0.
- Otherwise every part is below r. Add the parts up one by one until the running sum g first reaches r. If
  g ≤ P, the two groups have sums g and P + r − g, both between r and P, and the same identity finishes. If g > P,
  take three groups: the parts before the last one added, the last one, and the rest. Each group sum is below r,
  and three numbers A, Z, C ≤ M = r − 1 with sum P + r multiply to at least M²(P + r − 2M), because
  AZ − M(A + Z − M) = (M − A)(M − Z) ≥ 0, and once more for the third. Here g > P ≥ 5 forces r ≥ 4, and
  (r − 1)²(P − r + 2) ≥ Pr for P ≥ r ≥ 4.

For P = r = 3 the bound fails (2 · 2 · 2 < 3 · 3), which is the n = 6 exception.

**Step 3: n even.** Let r = n − P, which is prime; r ≤ P, since r is itself a candidate for P_n. P = 2 is
impossible (every part is at least 2), and P = 3 means n = 6, so P ≥ 5. Step 2 gives a(n) ≥ P · r. But P · r has
prime factors adding to n, so a(n) ≤ P · r. So a(n) = P · r, and P divides a(n): a contradiction.

**Step 4: n odd.** Now r = n − 3 − P is prime, r ≤ P as before, and 3 · P · r has prime factors adding to n, so it
is enough to show a(n) ≥ 3 · P · r. The odd parts of B are an odd number of odd primes, and its even parts are 2s.
P is odd (P = 2 would leave no parts at all), so r = n − 3 − P is even only if r = 2, which would make P even; so r
is odd too.

- *Some odd part w ≤ r.* Then w ≥ 3, so P ≥ 5. The other parts add up to P + (r + 3 − w), so by Step 2 they
  multiply to at least P(r + 3 − w), and a(n) ≥ w · P · (r + 3 − w) ≥ 3Pr, because
  w(r + 3 − w) − 3r = (w − 3)(r − w) ≥ 0.
- *Exactly one odd part u, and it is above r.* The rest are 2s adding to n − u > n − P = r + 3 ≥ 6, so there are
  at least four of them. Trading 2, 2, 2, 2 for 3, 5 keeps the sum and multiplies the product by 15/16, which
  contradicts the minimality of a(n).
- *Three or more odd parts, all above r.* Each is at least r + 2. Take two of them, U and V, and let C be the sum
  of all the other parts (at least r + 2). Then a(n) ≥ U · V · C, and as in Step 2, with M = r + 2,
  UVC ≥ M²(U + V + C − 2M) = (r + 2)²(P − r − 1). Since 3(r + 2) ≤ n gives P ≥ 2r + 3, this is at least 3Pr.

In every case a(n) ≥ 3Pr, so a(n) = 3Pr and P divides a(n): a contradiction. ∎

The idea in one line: a cheap number spends nearly all of n on one large prime, because once every factor is
small the product cannot stay below the two-prime (or three-prime) price.

## What was checked, and how

| Check | Result |
|---|---|
| `python3 A056240/check.py` | The conjecture holds for every composite n from 4 to 20000 except 6, computing a(n) by its own recursion and P_n from its definition; the equivalent form (largest prime factor of a(n) is at least P_n) for n ≤ 5000; the product bound of Step 2 for every P + r up to 160 |
| `lake build` | `A056240.sycamore_marcus` compiles; `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` |

The Lean theorem takes any `a : ℕ → ℕ` with the entry's definition as hypotheses: the prime factors of `a n` add up
to `n`, and `a n ≤ m` for every `m` whose prime factors add up to `n` (for n ≥ 2). The sum of prime factors is
`(Nat.primeFactorsList m).sum`. P_n is a hypothesis too, as `IsGreatest` of the set of primes p < n − 1 with
n − p prime (n even) or n − 3 − p prime (n odd), which is the comment's definition word for word. The conclusion
has both halves of "min": every allowed q gives at least a(n), and some allowed q gives exactly a(n).
`A056240.a0` (the least `m` found by `Nat.find`) meets the hypotheses, so they do not contradict each other, and
`A056240.sycamore_marcus_a0` states the result for it.

What Lean does not check: that `Nat.primeFactorsList` is what the OEIS means by "prime divisors taken with
multiplicity" (it is Mathlib's list of prime factors with multiplicity), and that P_n exists for a given n, which
for even n is Goldbach's conjecture and is not claimed.

## Novelty checks

Run on November 22 and again on November 23 2026, before and after the proof:

1. The entry, A288814 and A288313 (the related entries it links) show no proof and no claim that the conjecture is
   true or routine. Its only formulas are the bound a(n) ≥ n.
2. Nothing on those entries does the work: the bound a(n) ≥ n is far from the product bound above.
3. Web searches for the conjecture (the sequence's name with "largest prime factor", "Goldbach" and "proof") found
   only the OEIS entries.
4. The trureturing project has no issue and no file mentioning A056240 (searched with `gh api search/issues` and
   `gh search code`), nor A064364.

So no earlier proof was found. That is not a claim to be first.

## Not done

Nothing has been sent to the OEIS. A comment for the entry, if Linus wants to send one:

> The Sycamore-Marcus conjecture is true for every composite n != 6 for which P_n exists. Proof sketch: for any
> prime q | a(n), a(n) = q*a(n-q), so it suffices that the largest prime factor of a(n) is >= P_n. If all prime
> factors were < P_n, then, since integers >= 2 that are <= P with sum P+r (r <= P, P >= 5) have product >= P*r,
> one gets a(n) >= P_n*(n-P_n) for even n and a(n) >= 3*P_n*(n-3-P_n) for odd n (in the odd case, an a(n) with one
> odd prime factor and four 2's is impossible since 3*5 < 2^4). Both right sides have sopfr n, so a(n) would equal
> one of them and be divisible by P_n, a contradiction. The proof was found by an AI (Claude) and is formalized in
> Lean 4.
