# A154138: when is a triangular number plus 3 a square?

**Status: proved, and checked by Lean** (`SmallTrueThings/A154138.lean`, theorem `A154138.mathar`). November 25 2026.

## The conjecture

[A154138](https://oeis.org/A154138) is 1, 3, 12, 22, 73, 131, 428, 766, 2497, …: the k for which 3 + k(k+1)/2 is a
perfect square. So 12 is in it because 3 + 78 = 81 = 9², and 22 because 3 + 253 = 256 = 16².

R. J. Mathar, who made the entry in October 2009, gave two formulas and marked both as conjectures:

> a(n) = +a(n-1) +6\*a(n-2) -6\*a(n-3) -a(n-4) +a(n-5);
>
> G.f.: x\*(1 + 2\*x + 3\*x^2 - 2\*x^3 - 2\*x^4)/((1-x)\*(x^2-2\*x-1)\*(x^2+2\*x-1)).

Zak Seidov added that he believed both, and gave the shorter form a(1..4) = 1, 3, 12, 22 and
a(n) = 6a(n−2) − a(n−4) + 2 for n > 4. All three are true.

## The proof

**Step 1: a Pell equation.** Put x = 2k + 1. Then 8(3 + k(k+1)/2) = 4k² + 4k + 24 = x² + 23, so
3 + k(k+1)/2 = y² exactly when

  x² + 23 = 8y².

The question is which odd x > 0 solve this. (Every solution has x odd, since x² ≡ 1 mod 8.)

**Step 2: the descent.** If (x, y) is a solution with y ≥ 6, so is (x', y') = (3x − 8y, 3y − x), because
(3x − 8y)² − 8(3y − x)² = x² − 8y² identically. It is a smaller positive solution: from x² = 8y² − 23,

- 3x ≥ 8y, since 9x² = 72y² − 207 ≥ 64y² once 8y² ≥ 207;
- x ≤ 3y, since x² < 9y²;
- x > 2y, since x² = 8y² − 23 > 4y² once 4y² > 23, so y' = 3y − x < y.

The map undoes (x, y) ↦ (3x + 8y, x + 3y), multiplication by the unit 3 + √8. So every solution is reached from a
solution with y ≤ 5 by applying (x, y) ↦ (3x + 8y, x + 3y) some number of times. For y ≤ 5 the only solutions are
(3, 2) and (7, 3).

**Step 3: the order.** Write s₀ = (3, 2), s₁ = (7, 3) and s_{n+2} = (3x + 8y, x + 3y) of s_n. By Step 2 these are
all the solutions. They are already in increasing order: if s_n < s_{n+1} < step(s_n) in both coordinates, the same
holds one place on, because the step map is increasing in both coordinates. The base case is
(3, 2) < (7, 3) < (25, 9). So the n-th term of the sequence is a(n) = (x_{n−1} − 1)/2.

**Step 4: the recurrences.** Two steps of the map send x to 17x + 48y, and 6(3x + 8y) − x is the same thing, so
x_{n+4} = 6x_{n+2} − x_n. With x = 2a + 1 this is Seidov's a(n) = 6a(n−2) − a(n−4) + 2. Subtracting Seidov's
formula at n − 1 from Seidov's formula at n removes the constant 2 and gives Mathar's five-term recurrence. The
denominator of the generating function multiplies out to 1 − x − 6x² + 6x³ + x⁴ − x⁵, so the g.f. says exactly
that the five-term recurrence holds from n = 6 on and that the first five terms are 1, 3, 12, 22, 73. ∎

The idea in one line: the solutions come in two chains of the unit 3 + √8, starting from 3 + 2√8 and 7 + 3√8, and
the two chains interleave, which is why the recurrence skips one term.

## What was checked, and how

| Check | Result |
|---|---|
| `python3 A154138/check.py` | Every k ≤ 3·10⁷ with 3 + k(k+1)/2 a square, by brute force, is a term of the recurrence and vice versa; every solution of x² + 23 = 8y² with y ≤ 2·10⁸ (so k up to about 5.6·10⁸), found by testing each y directly, is a term; 400 terms of the recurrence (the last has 153 digits) are all in the set; Mathar's and Seidov's recurrences and the g.f. agree for 400 terms; the descent from each of the first 60 solutions ends at (3, 2) or (7, 3) |
| `lake build` | `A154138.mathar` compiles; `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` |

The Lean theorem takes any `a : ℕ → ℕ` that lists the set in increasing order, indexed from 1 as on the entry:
`a n < a (n+1)` for n ≥ 1, and k is in the set {k : ∃ m, 3 + k(k+1)/2 = m²} exactly when k = a n for some n ≥ 1.
The set is written as the entry defines it, with natural-number division by 2. The conclusion has four parts: the
first four terms, Seidov's recurrence for n ≥ 5, Mathar's five-term recurrence for n ≥ 6, and the g.f. as an
identity of power series over ℤ, den · A = num, where A = Σ_{n≥1} a(n)xⁿ and den, num are the entry's denominator
and numerator, typed as printed. `A154138.listing` is a concrete listing, built from the two chains, and
`A154138.listing_spec` shows that it meets the hypotheses, so they do not contradict each other.

What Lean does not check: that den · A = num is what "G.f.: num/den" means. It is, since den has constant term 1
and so is invertible in the power series ring, but the file states the multiplied-out form.

## Novelty checks

Run on November 25 2026, before the proof was started:

1. The entry has no proof. Seidov's comment says only that he believes the conjectures. It links a SeqFan
   discussion by F. T. Adams-Watters, October 2009; that message is not in the Internet Archive. The one message of
   the thread that is archived is about a different question, which shifts c make k(k+1)/2 + c a square for some
   k, and has no proof of these formulas.
2. No formula on the entry or its cross-references (A000217, A000290, A006451) gives the solutions. The fact that
   does the work, the two chains of x² − 8y² = −23, is standard Pell-equation theory but appears nowhere on them.
3. Web searches for the entry with "triangular" and "square", and for the equation x² − 8y² = −23, found only the
   OEIS entry and its sibling list A154153.
4. The trureturing project has no issue and no file mentioning A154138, nor any of its siblings A006451 and
   A154139 to A154147, nor A154153 (searched with `gh api search/issues` and `gh search code`).

Added later the same day, while working on the sibling A154145: two siblings that A154138 does not link carry the
method. On A154142 Robert Israel wrote in 2015 that its conjectures "follow from the theory of Pell-like equations",
with closed forms, and A154146 links his 2019 proof of its recurrence. Neither covers c = 3, but they confirm that the
method is known for this family; the check above searched only A154138's own links.

So no earlier proof was found. That is not a claim to be first, and the method is the textbook one: a specialist
would find this proof routine. What was missing was the proof written down.

## Not done

Nothing has been sent to the OEIS. A comment for the entry, if Linus wants to send one:

> The conjectures are true. With x = 2k+1, 3 + k(k+1)/2 = y^2 is x^2 - 8*y^2 = -23. For y >= 6 the map
> (x,y) -> (3x-8y, 3y-x) sends a positive solution to one with smaller positive y, so all solutions are obtained
> from (3,2) and (7,3) by (x,y) -> (3x+8y, x+3y), and the two chains interleave in increasing order. Hence
> x(n+4) = 6*x(n+2) - x(n), which is a(n) = 6*a(n-2) - a(n-4) + 2 and gives the recurrence and g.f. The proof was
> found by an AI (Claude) and is formalized in Lean 4.
