# A156253: a nested recurrence for the run numbers of the Kolakoski sequence

**Status: proved, and checked by Lean** (`SmallTrueThings/A156253.lean`, theorems `A156253.maiga` and
`A156253.maiga_gcd`). November 20 2026. **Not a new truth:** see "What was known" below.

## The conjecture

The Kolakoski sequence [A000002](https://oeis.org/A000002) is made of 1's and 2's, starts with 1, and describes
itself: its n-th term is the length of its n-th run.

```
K = 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 2, ...
    runs:  1 | 2 2 | 1 1 | 2 | 1 | 2 2 | 1 | 2 2 | 1 1 | 2 | ...
```

[A156253](https://oeis.org/A156253) is the number of the run each position lies in:

```
a = 1, 2, 2, 3, 3, 4, 5, 6, 6, 7, 8, 8, 9, 9, 10, ...
```

(In the entry's words, a(n) is the least k with A054353(k) ≥ n, where A054353 are the partial sums of K.) The entry
carries this comment by Jon Maiga, dated December 9 2021:

> Conjecture: a(n) = (a(a(n-1)) mod 2) + a(n-2) + 1.

## The proof

Two facts, both restatements of the definition.

1. **K(m) = 1 exactly when a(m) is odd.** Position m lies in run a(m), and the runs alternate 1's, 2's, 1's, …
   starting with 1's.
2. **Run j has length K(j).** That is the self-description.

Take n ≥ 3 and let j = a(n−1), the run of the position before n. By fact 2 its length is K(j), and by fact 1 with
m = j that length is 1 exactly when a(j) = a(a(n−1)) is odd.

- **Length 1.** Run j is the single position n−1. So n−2 lies in run j−1 and n in run j+1: a(n) = a(n−2) + 2.
- **Length 2.** Run j is {n−2, n−1} or {n−1, n}. In the first case a(n−2) = j and a(n) = j+1; in the second
  a(n−2) = j−1 and a(n) = j. Either way a(n) = a(n−2) + 1.

So a(n) = a(n−2) + 1 + (a(a(n−1)) mod 2). ∎

The same two cases give the sibling formula a(n) = a(n − gcd(a(a(n−1)), 2)) + 1: the gcd is the length of run j,
and a(n) is one more than a(n−1) when that length is 1, one more than a(n−2) when it is 2.

## What it means

The sequence is asked about itself twice: once for which run the previous position is in, and once for which run
*that number* is in, whose parity is a term of K. Since a(n) ≤ n, the recurrence with a(1) = 1, a(2) = 2 computes
every term from earlier ones, and K(n) is 1 or 2 as a(n) is odd or even. So it is a definition of the Kolakoski
sequence that never mentions runs. The Lean file uses it that way: `kol` is defined from the recurrence, and
`kol_isKolakoski` proves that the result is cut into runs whose lengths are its own terms.

## What was known

- The conjecture's author, Jon Maiga, wrote a note linked from the entry,
  [A Recurrence Related to the Kolakoski Sequence](https://oeis.org/A156253/a156253.pdf) (2025). Its Theorem 4
  proves the sibling formula by the same three cases, and it says of the conjecture: "A proof for this variation
  of a_n can be constructed in a similar way." So nobody doubted this one; the entry still lists it as a conjecture
  and the note does not write the proof out.
- Fact 1 is Benoit Cloitre's formula K(n) = gcd(a(n), 2) on the A000002 entry.
- The automated project [the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing)
  lists A156253 in its file of candidates it screened out; a search of its issues and code on November 20 2026
  found no proof.
- A web search on November 20 2026 for the conjecture found Maiga's note and nothing else on it.

What this adds: the proof of the conjectured form written out, a formal proof of both forms from a precise
definition, and a formal construction of a Kolakoski sequence. Mathlib at the pinned version contains nothing named
Kolakoski.

## What was checked, and how

| Check | Result |
|---|---|
| `python3 A156253/check.py 1000000` | Both recurrences hold for 3 ≤ n ≤ 1,000,000 on the sequence built from its definition; the first terms match the OEIS; the recurrence alone rebuilds the sequence |
| `lake build` | `A156253.maiga`, `maiga_gcd`, `kol_isKolakoski` compile; `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` |

The Lean theorems take any `K` and `a` with two hypotheses:

- `IsKolakoski K`: every term is 1 or 2, and for each k ≥ 1 the positions S(k−1)+1, …, S(k) hold 1's when k is odd
  and 2's when k is even, where S(k) = K(1) + … + K(k). The length of block k is K(k) by the way S is defined, and
  the blocks alternate, so they are the runs.
- `a n` is the least k with n ≤ S(k), which is the entry's definition of A156253.

That reading of "the n-th term is the length of the n-th run" is the one thing a reader has to accept: the
definitions `S` and `IsKolakoski` at the top of the file.

## Not done

Nothing has been sent to the OEIS. A comment for the entry, if Linus wants to send one:

> The conjecture is true. Let j = a(n-1). Run j of A000002 has length A000002(j) = gcd(a(j), 2) (Cloitre), so it has
> length 1 iff a(a(n-1)) is odd. If its length is 1 it is {n-1}, so a(n) = a(n-2) + 2. If its length is 2 it is
> {n-2, n-1} or {n-1, n}, and in both cases a(n) = a(n-2) + 1. This is the argument of Maiga's note applied to the
> other formula. Both formulas are formalized in Lean 4; the proof was written by an AI (Claude).
