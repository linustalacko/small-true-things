# A154153 and its family: when is a triangular number plus c a square?

**Status: proved for every c ≥ 1, and with it Mathar's conjectures on eight entries, checked by Lean**
(`SmallTrueThings/A154153.lean`: the general theorem `A154153.chains`, its corollary `A154153.six`, and one
theorem per entry, `A154153.a154141` to `A154153.a154154`). November 26 2026.

## The conjectures

Fix c ≥ 1 and list the k for which c + k(k+1)/2 is a perfect square. In October 2009 R. J. Mathar made an OEIS
entry for each c up to 30 that gives a nonempty list ([A175032](https://oeis.org/A175032) gives the index). For
most of them he gave two formulas, marked as conjectures:

> a(n) = a(n-1) + 6\*a(n-2) - 6\*a(n-3) - a(n-4) + a(n-5),

and a generating function with denominator (x−1)(x²−2x−1)(x²+2x−1). On eight of the entries, read on the OEIS
data mirror on November 26 2026, both are still marked as conjectures:

| Entry | c | Starts | g.f. numerator as printed |
|---|---|---|---|
| [A154141](https://oeis.org/A154141) | 8 | 1, 7, 16, 46, 97 | x(1+6x+3x²−6x³−2x⁴), over (1−x)(…) |
| [A154143](https://oeis.org/A154143) | 10 | 3, 5, 26, 36, 155 | x(3+2x+3x²−2x³−4x⁴), over (1−x)(…) |
| [A154144](https://oeis.org/A154144) | 13 | 2, 8, 23, 53, 138 | x(2+6x+3x²−6x³−3x⁴), over (1−x)(…) |
| [A154148](https://oeis.org/A154148) | 21 | 5, 7, 40, 50, 237 | x(−5−2x−3x²+2x³+6x⁴) |
| [A154150](https://oeis.org/A154150) | 24 | 1, 15, 24, 94, 145 | x(−1−14x−3x²+14x³+2x⁴) |
| [A154151](https://oeis.org/A154151) | 25 | 0, 18, 21, 111, 128 | x²(−18−3x+18x²+x³) |
| [A154153](https://oeis.org/A154153) | 28 | 6, 8, 47, 57, 278 | x(−6−2x−3x²+2x³+7x⁴) |
| [A154154](https://oeis.org/A154154) | 30 | 3, 13, 34, 84, 203 | x(−3−10x−3x²+10x³+4x⁴) |

This project proved two other members one at a time the day before: [A154138](../A154138/README.md) (c = 3) and
[A154145](../A154145/README.md) (c = 15, where the shape is different). Doing it once for every c is the better form.

## The theorem

Put x = 2k + 1 and N = 8c − 1. Then 8(c + k(k+1)/2) = x² + N, so k is in the set exactly when

  x² + N = 8y² for some y.

Call a member *small* when x² < 8N, and let T(k) = 3k + 1 + 4y. In (x, y) coordinates T is
(x, y) ↦ (3x + 8y, x + 3y), multiplication by the unit 3 + √8.

**Theorem.** Let a(0) < a(1) < a(2) < … list the members, and let m be the number of small ones. Then for every n,

  a(n + m) = T(a(n)),  and so  a(n + 2m) = 6·a(n + m) − a(n) + 2.

No condition on how the chains of solutions interleave is needed. It holds for every c.

**Proof.** Four facts about T, each a line of algebra with x² + N = 8y²:

1. *T maps members to members.* (3x + 8y)² + N = 8(x + 3y)².
2. *T is strictly increasing on members.* A larger k has a larger x, so a larger y.
3. *T never lands on a small member.* (3x + 8y)² ≥ 64y² = 8x² + 8N ≥ 8N.
4. *Every member that is not small is T of a member.* If x² ≥ 8N, put x' = 3x − 8y and y' = 3y − x. Then
   8y ≤ 3x (because 64y² = 8x² + 8N ≤ 9x²), and x ≤ 3y (because x² < 8y²). So x' and y' are natural numbers, x' is
   odd, x'² + N = 8y'², and (3x' + 8y', x' + 3y') = (x, y).

Small members come before all others, since being small is a bound on k. So the members from a(m) on are exactly
the members that are not small, and by 3 and 4 these are exactly the values T(a(n)). Both n ↦ a(n + m) and
n ↦ T(a(n)) are strictly increasing (the second by 2), and they have the same range. Two strictly increasing
listings of the same set are equal, so a(n + m) = T(a(n)).

For the second formula, T(T(k)) = 17k + 8 + 24y, which is 6·T(k) − k + 2. ∎

**The eight entries.** For each of them a finite search shows exactly two small members, so m = 2. For c = 30, for
example, the small k satisfy (2k+1)² < 1912, so k ≤ 21, and only k = 3 and k = 13 are members. This gives
a(n) = 6a(n−2) − a(n−4) + 2 from n = 5 on. Subtracting the same formula at n − 1 removes the 2 and gives Mathar's
recurrence from n = 6 on. The denominator multiplies out to −1 + x + 6x² − 6x³ − x⁴ + x⁵, so each g.f. says exactly
that the recurrence holds and that the first five terms are as printed.

The idea in one line: the members that are not images of the unit are the ones below a fixed bound, so the listing
repeats itself under the unit after exactly that many terms.

## What was checked, and how

| Check | Result |
|---|---|
| `python3 A154153/check.py` | For every c from 1 to 300, the members k ≤ 2·10⁶ found by brute force satisfy a(n+m) = T(a(n)), with m = the number of small members (m is 0, 2, 4 or 6 in that range), and the small members are exactly those not of the form T(k). For the eight entries, m = 2, every printed term agrees, and Mathar's recurrence and printed g.f. agree with 400 terms of a(n) = 6a(n−2) − a(n−4) + 2, all of them members |
| `lake build` | Everything compiles; `#print axioms` on `chains`, `six`, `listing_spec` and the eight entry theorems shows only `propext`, `Classical.choice`, `Quot.sound` |

What Lean checks:

- `A154153.chains`: for every c ≥ 1, every strictly increasing `a : ℕ → ℕ` whose values are exactly
  {k : ∃ m, c + k(k+1)/2 = m²}, and every m such that the first m values are exactly the small ones,
  a(n+m) = T(a(n)). `A154153.six` adds a(n+2m) = 6a(n+m) − a(n) + 2.
- `A154153.a154141` and the seven like it: the entry's own hypotheses, written as the entry prints them (offset 1,
  natural-number division), imply the first five terms, a(n) = 6a(n−2) − a(n−4) + 2 for n ≥ 5, Mathar's recurrence
  for n ≥ 6, and den · A = num for the entry's numerator and denominator as printed, with A = Σ_{n≥1} a(n)xⁿ over ℤ.
  In each, "exactly two small members" is proved inside Lean by a case search over k and y.
- `A154153.listing_spec`: the set is infinite, and its increasing listing (`Nat.nth`) meets the hypotheses for each
  of the eight values of c, so the hypotheses are not contradictory.

What Lean does not check: that den · A = num is what "G.f.: num/den" means. It is, since den has constant term ±1 and
so is invertible. The partial-fraction g.f. each entry prints second was not formalized, and `check.py` does not test
it either. The general theorem does not compute m for a given c. That is a finite search, done here for the eight
entries only.

## Novelty checks

Run on November 26 2026, before the proof was started:

1. **The entries.** All eight still mark their formulas as conjectures. Each links a message in F. T. Adams-Watters's
   SeqFan thread of October 2009: message 002504, the one A154138 links, and for A154143 message 002506. As recorded
   in `A154138/README.md`, 002504 is not in the Internet Archive, and the one archived message of the thread has no
   proof. The Wayback availability check found no snapshot of 002506 either, so neither message was read. A154151 has Harvey P. Dale's note that the recurrence holds for 1000 terms. A154153 links a picture by
   David A. Corneth titled "Conjectured formula", which was not read. Two siblings are not in the eight because they
   no longer mark their formulas as conjectures (A154149, A154152; the latter has b-files and an index entry).
2. **Corollaries.** Nothing on the entries or on their cross-references (A000217, A000290, A006451, A175032) gives
   the solutions. On the sibling A154142, Robert Israel wrote in 2015 that its conjectures "follow from the theory of
   Pell-like equations", and he proved A154146 in a linked note in 2019. So the method is known for this family, and
   a specialist would find each case routine. Neither treats the other values of c or states the general form.
3. **Web.** Searches for the recurrences, for "triangular number plus" a constant being a square, and for the
   equation x² − 8y² = 1 − 8c with the interleaving found textbook material on square triangular numbers (c = 0) and
   the related entry A006452. None gave a proof for these entries or the general statement.
4. **trureturing.** `gh api search/issues` and `gh search code` found nothing for A154141, A154143, A154144, A154148,
   A154150, A154151, A154153, A154154, or A175032.

So no earlier proof was found. That is not a claim to be first. The method is the classical one for generalized Pell
equations. What was missing was a written proof of these formulas. The observation that the interleaving never needs
checking, because the first m members are exactly the ones not reached by the unit, may be worth stating on its own.

## Not done

- A154144 carries Zizka's comment "a(n) = 6\*a(n-2) - a(n-4) + 2, for n>2". It cannot start at n = 3, since a(−1)
  does not exist. The theorem here gives it from n = 5 on, as Zizka wrote it on A154141 and A154143. "n>4" is
  presumably meant.
- Nothing has been sent to the OEIS. A comment for each of the eight entries, if Linus wants to send them (shown for
  A154153; the others change c, the two base members and the bound):

> Mathar's conjectures are true. With x = 2k+1, 28 + k(k+1)/2 = y^2 is x^2 + 223 = 8*y^2. If x^2 >= 8*223, then
> (x', y') = (3x-8y, 3y-x) is a solution in nonnegative integers with (x, y) = (3x'+8y', x'+3y'). So every term
> except a(1) = 6 and a(2) = 8 (the only k with (2k+1)^2 < 1784) is T(a(j)) for an earlier term, where
> T(k) = 3k+1+4y. T is increasing and never gives a k with (2k+1)^2 < 1784, so a(n+2) = T(a(n)). Hence
> a(n) = 6*a(n-2) - a(n-4) + 2 for n > 4, which gives the recurrence and the g.f. The same argument shows that for
> every c the members satisfy a(n+m) = T(a(n)), where m is the number of members with (2k+1)^2 < 8(8c-1). The proof
> was found by an AI (Claude) and is formalized in Lean 4.
