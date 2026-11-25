# A154145: when is a triangular number plus 15 a square?

**Status: Mathar's conjectures proved and Zizka's formula refuted, checked by Lean**
(`SmallTrueThings/A154145.lean`, theorem `A154145.mathar`). November 25 2026.

## The conjectures

[A154145](https://oeis.org/A154145) is 1, 4, 6, 11, 20, 33, 43, 70, 121, 196, …: the k for which 15 + k(k+1)/2 is a
perfect square. So 11 is in it because 15 + 66 = 81 = 9².

R. J. Mathar, who made the entry in October 2009, gave two formulas and marked both as conjectures:

> a(n)= +a(n-1) +6\*a(n-4) -6\*a(n-5) -a(n-8) +a(n-9).
>
> G.f.: x\*(-1-3\*x-2\*x^2-5\*x^3-3\*x^4+5\*x^5+2\*x^6+3\*x^7+2\*x^8)/((x-1) \* (x^4+2\*x^2-1) \* (x^4-2\*x^2-1)).

The entry also carries a comment, a(1..4) = (1,4,6,11); a(n>4) = 6a(n−2) − a(n−4) + 2 (Ctibor O. Zizka, 2009), and
the same line among its formulas. That is the form that holds for the siblings A154138 to A154144, and here it is
false at its first use: a(5) = 20, but 6·a(3) − a(1) + 2 = 37. Mathar's two formulas are true. The difference is
that this equation has four chains of solutions where the siblings have two.

## The proof

**Step 1: a Pell equation.** Put x = 2k + 1. Then 8(15 + k(k+1)/2) = x² + 119, so 15 + k(k+1)/2 = y² exactly when

  x² + 119 = 8y².

**Step 2: the descent.** If (x, y) is a solution with y ≥ 12, so is (x', y') = (3x − 8y, 3y − x), since
(3x − 8y)² − 8(3y − x)² = x² − 8y². It is a smaller solution in natural numbers: from x² = 8y² − 119,

- 3x ≥ 8y, since 9x² = 72y² − 1071 ≥ 64y² once 8y² ≥ 1071, which holds for y ≥ 12;
- x ≤ 3y, since x² < 9y²;
- x > 2y, since x² = 8y² − 119 > 4y² once 4y² > 119, so y' = 3y − x < y.

The map undoes (x, y) ↦ (3x + 8y, x + 3y), multiplication by the unit 3 + √8. So every solution is reached from one
with y ≤ 11 by that step. For y ≤ 11 there are exactly four: (3, 4), (9, 5), (13, 6) and (23, 9).

**Step 3: the order.** Put s₀, …, s₃ = (3, 4), (9, 5), (13, 6), (23, 9) and s_{n+4} = step(s_n). By Step 2 these
are all the solutions. They are in increasing order: if s_n < s_{n+1} < s_{n+2} < s_{n+3} < step(s_n), componentwise,
the same holds one place on, because the step is increasing in both coordinates. The base case is
(3, 4) < (9, 5) < (13, 6) < (23, 9) < (41, 15). So a(n) = (x_{n−1} − 1)/2.

**Step 4: the recurrences.** Two steps send x to 17x + 48y, which is 6(3x + 8y) − x, so x_{n+8} = 6x_{n+4} − x_n.
With x = 2a + 1 this is a(n) = 6a(n−4) − a(n−8) + 2 for n ≥ 9. Subtracting the same formula at n − 1 removes the 2
and gives Mathar's recurrence for n ≥ 10. The g.f.'s denominator multiplies out to −1 + x + 6x⁴ − 6x⁵ − x⁸ + x⁹,
so the g.f. says exactly that Mathar's recurrence holds from n = 10 on and that the first nine terms are
1, 4, 6, 11, 20, 33, 43, 70, 121. ∎

The idea in one line: the solutions form four chains of the unit 3 + √8, and taken in turn the chains are already in
order, so the recurrence looks four places back, not two.

## What was checked, and how

| Check | Result |
|---|---|
| `python3 A154145/check.py` | Every k ≤ 3·10⁷ with 15 + k(k+1)/2 a square, by brute force, is a term of the recurrence and vice versa; every solution of x² + 119 = 8y² with y ≤ 2·10⁸, found by testing each y directly, is a term; 400 terms of the recurrence are in the set; the g.f. and Mathar's recurrence agree with them for 400 terms; the solutions with y ≤ 11 are the four base pairs, and the descent from each of the first 80 solutions ends at one of them; Zizka's form fails at every n from 5 to 400 |
| `lake build` | `A154145.mathar` compiles; `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` |

The Lean theorem takes any `a : ℕ → ℕ` that lists the set in increasing order, indexed from 1 as on the entry:
`a n < a (n+1)` for n ≥ 1, and k is in {k : ∃ m, 15 + k(k+1)/2 = m²} (natural-number division, as the entry writes
it) exactly when k = a n for some n ≥ 1. It concludes the first nine terms, the four-chain form for n ≥ 9, Mathar's
recurrence for n ≥ 10, den · A = num for the entry's numerator and denominator as printed (A = Σ_{n≥1} a(n)xⁿ over
ℤ), and the negation of Zizka's form. `A154145.listing` is a concrete listing built from the four chains, and
`A154145.listing_spec` shows it meets the hypotheses, so they do not contradict each other.

What Lean does not check: that den · A = num is what "G.f.: num/den" means. It is, since den has constant term −1
and so is invertible in the power series ring. The entry's second g.f., a partial-fraction form, was not
formalized; `check.py` does not test it either.

## Novelty checks

Run on November 25 2026, before the proof was started:

1. The entry has no proof. Its one link is the SeqFan thread of October 2009 that A154138 also links; as recorded
   in `A154138/README.md`, the archived part of that thread has no proof of these formulas.
2. Nothing on the entry or its cross-references (A000217, A000290, A006451) gives the solutions. One thing
   bears on the method: on the sibling A154142, Robert Israel wrote in 2015 that its conjectures "follow from the
   theory of Pell-like equations" and gave closed forms, and he proved the sibling A154146 in a linked note in 2019.
   So the method is known to work for this family, and a specialist would find this proof routine. Neither sibling
   is linked from A154145, and neither treats c = 15, where the four chains change the shape of the answer.
3. Web searches for the entry, for "15 plus the k-th triangular number" with "square", and for the recurrence found
   only the OEIS entry and its sibling list.
4. The trureturing project has no issue and no file mentioning A154145 (`gh api search/issues`,
   `gh search code`).

So no earlier proof was found. That is not a claim to be first. The refutation of Zizka's line is one line of
arithmetic that anyone checking it would have seen. What was missing was a written proof of Mathar's formulas and a
note that the two-step form does not hold here.

## Not done

Nothing has been sent to the OEIS. A comment for the entry, if Linus wants to send one:

> Mathar's conjectures are true, and the formula a(n) = 6*a(n-2) - a(n-4) + 2 is not: a(5) = 20, not 37.
> With x = 2k+1, 15 + k(k+1)/2 = y^2 is x^2 - 8*y^2 = -119. For y >= 12 the map (x,y) -> (3x-8y, 3y-x) sends a
> solution to one with smaller y, so all solutions come from (3,4), (9,5), (13,6), (23,9) by
> (x,y) -> (3x+8y, x+3y), and the four chains interleave in increasing order. Hence x(n+8) = 6*x(n+4) - x(n),
> i.e., a(n) = 6*a(n-4) - a(n-8) + 2 for n > 8, which gives Mathar's recurrence and g.f. The proof was found by an
> AI (Claude) and is formalized in Lean 4.
