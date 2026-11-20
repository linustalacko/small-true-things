# Notebook

What I tried, what worked and what did not. Each session reads this first and adds to it. Newest entry first; the
queue at the bottom is where the next one starts.

## 2026-11-20: A040027, Gould numbers from alternating factorials. Proved.

- **Chosen** because a count of set partitions equal to a signed sum with factorials in it should not work, and
  does. Yanev, 2021; no proof on the entry.
- **The idea.** Put the right side into the Gould recurrence. One Stirling identity (remove the block of the last
  element) turns the sum of earlier terms into the same sum with the column shifted by one. What is left over is
  Σ (−1)^k k! S(n+1,k+1), which is 0. The first-session sketch used generating functions; the finite sums are
  shorter and are what Lean wants.
- **What it means.** The alternating factorials are forced: their differences are the first column of the inverse
  Stirling matrix. The conjecture is Stirling orthogonality summed once. Worth trying on other "conjecture: a(n) =
  Σ (odd sequence) · Stirling" comments: compute what the differences would have to be.
- **Lean.** `SmallTrueThings/A040027.lean`. Two errors on the first run, both trivial. Things that helped:
  - Write `n + 1 + 1`, never `n + 2`, in anything `rw` must match after an induction.
  - Give `sum_range_succ` and `sum_range_succ'` the function explicitly when two sums are in the goal.
  - Extend a triangular sum to a rectangle with `sum_subset` and `stirlingSecond_eq_zero_of_lt`, then plain
    `sum_comm`.
  - Work in ℤ with casts from the start when signs appear; `push_cast` then `ring`.
- **Reusable.** `A040027.stirlingSecond_succ_succ_eq_sum_choose` (S(n+1,m+1) = Σ C(n,j) S(j,m)) and
  `A040027.alternating_sum` are not in Mathlib. `A005121.stirlingSecond_eq_H` is the complete-homogeneous form.
  Move them to a shared file the third time one is needed.

## 2026-11-20: A005121, Mohapatra's triangle. Proved.

The first one, taken end to end to see whether the loop works. It does.

- **Chosen** from 110 entries because the rule looked unmotivated (why multiply by k and sum a tail?) and the
  sequence is a good one: chains in the partition lattice. Posted three weeks ago, no proof on the entry.
- **The idea.** Unroll the rule. Going down from row n you pick weakly increasing column numbers and multiply them
  until you hit a diagonal entry, so the coefficients are complete homogeneous symmetric polynomials of k, …, m.
  Sorting multisets by their least element is the same shape as the rule, and it telescopes into a Stirling number.
  About ten minutes on paper.
- **A bonus** the conjecture did not ask for: R(n,k) counts the chains whose first step keeps 1, …, k apart and
  puts k+1 with one of them. Brute force agrees for n ≤ 8.
- **Lean.** `SmallTrueThings/A005121.lean`, about 200 lines, compiled on the first run. What made it easy: stating
  the theorem over any `R` and `a` with the OEIS rules as hypotheses (nothing to define, nothing to trust), and
  defining `H` by the least-element recursion so it matches the rule term for term. `Finset.sum_comm'` with
  `simp only [mem_Icc]; omega` does every swap of a triangular double sum.
- **Guard against a vacuous theorem.** Hypotheses that contradict each other prove anything, so the file also builds
  a concrete `T` and `L` that obey them. Do this every time the theorem is stated over hypotheses.

## How the loop runs

1. Pick a conjecture from the queue, or harvest more. Take the one that is most beautiful, not the hardest.
2. `<A-number>/check.py`: reproduce it, far past where the author checked.
3. Prove it or find the counterexample. Look on the entry and its links for a proof first.
4. `SmallTrueThings/<A-number>.lean`, imported from `SmallTrueThings.lean`. `lake build`, then `#print axioms`.
5. `<A-number>/README.md`: one page, with what was and was not machine-checked.
6. An entry here, and a row in the README's table.

Nothing goes to the OEIS, or anywhere public, without Linus.

Since 2026-11-20 this runs once a day at about 1 pm, from the scheduled task `small-true-things-daily` in the Claude
desktop app (`~/.claude/scheduled-tasks/small-true-things-daily/SKILL.md`). Each run starts with no memory, so
whatever the next run needs to know goes in this file. An unfinished day is an entry too.

## Things to know

- **The OEIS refuses fast readers.** `https://oeis.org/search?q=…&fmt=json&start=N` gives ten entries a page; after
  eleven pages at 1.2 s apart it answered 403 for the rest of the run, and worked again some minutes later. Fetch a
  few pages a session, slowly, and keep what comes back in `scratch/`. One entry: `search?q=id:A040027&fmt=json`.
- **Core sequences are picked clean.** Their conjectures are famous open problems or already settled; `-keyword:core`
  helps. Sela Fried has been settling Velin Yanev's conjectures since late 2025, so read the links before starting
  one of those.
- **Setup.** Lean 4.37.0-rc1 with Mathlib, through `elan` from Homebrew. `.lake` is 7.8 GB and `~/.elan` 3.3 GB.
  `lake exe cache get` after any Mathlib bump, or it compiles Mathlib from source.
- `lake env lean scratch/Probe.lean` runs a throwaway file against the build.

## Queue

Seen in the first harvest (`"Conjecture: a(n) =" -keyword:core`, first 110 results) and not yet settled on the
entry as of 2026-11-20. My guess at each is a guess.

| Entry | Conjecture | First look |
|---|---|---|
| A006068 | Inverse Gray code: a(n) = a(A053645(A063946(n))) + A053644(n) (Kurkov, 2023) | Looks true by a bit argument: flip the second bit, drop the first. Bitwise Lean may be fiddly |
| A034448 | usigma(n) = sigma(n²/rad(n)) / sigma(n/rad(n)) (Yanev, 2017) | True on prime powers and both sides are multiplicative. Check Fried's link on A001157 first |
| A129527 | a(n) = 2n − (odd part of n) (Yanev, 2017) | One line of induction, which Arndt sketched on the entry. A warm-up at most |
| A003278 | Szekeres's sequence in terms of A191107 and A055246 (Jeffery, 2015) | Not looked at; base 3 |
| A034836 | n = xyz with x ≤ y ≤ z: (np + 3·nsq + 2·ntp)/6 | Burnside, probably |
| A175254 | a(n) = Σ_k A006218(n−k) (Mathar, 2012) | As I read it, it fails at n = 2 (5 against 4). Read the entry properly before believing that |
| A056240 | a(n) = min of q · a(n−q) over certain primes q | Not looked at |
