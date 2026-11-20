# Notebook

What I tried, what worked and what did not. Each session reads this first and adds to it. Newest entry first; the
queue at the bottom is where the next one starts.

## The rule: new results only

Linus, 2026-11-20, after the third result turned out to be one its author already knew: "only work on new things,
not things to be known as true". Before any proof is started, a candidate has to pass all four checks:

1. The entry and everything it links to show no proof, and nobody there says it is true or that a proof is routine.
2. It is not a short corollary of a formula already on the entry or its cross-references.
3. A web search for the conjecture finds no proof.
4. `the-omega-institute/trureturing` has no issue or file for the A-number.

A candidate that fails gets one line under "Ruled out" below, so no run tries it again. If nothing passes on a
given day, the day is spent harvesting and screening, and that is the day's entry. Nothing known goes in the
results table from now on. By this rule the first three would have gone differently: A005121 fails check 4,
A156253 fails check 1, and A040027 passes.

## 2026-11-20: A156253, the Kolakoski run numbers. Proved; known to be true.

- **How it was chosen, which is the real entry.** The search for earlier proofs was done first this time, and it
  removed three picks in a row. A226857 (sums and products of Fibonacci numbers, Barker 2014): I had a proof
  sketched (F_k F_l = F_{k+l-2} + F_{k-2} F_{l-2}, so only F_k, 2F_k, 3F_k qualify) and then found trureturing
  proved it in September. A006068 (Kurkov, Gray code): they settled it. A145920 (pentagonal and C(n,4)): the key
  fact, C(n,4) is pentagonal exactly when 3 does not divide n, is already a formula on the entry.
  Ten minutes of searching saved a day each time.
- **Why this one anyway.** It is the most beautiful thing in the two harvests: the Kolakoski sequence asked about
  itself twice. Its author's own note proves a sibling formula and says this one "can be constructed in a similar
  way", so its truth was not in doubt. What did not exist was the written proof, a formal proof, and a Kolakoski
  sequence in Lean. The README says exactly that. This is the pattern to follow when a result is known: say so
  first, then say what is added.
- **The idea.** Run j = a(n-1) has length K(j), and K(j) = 1 exactly when a(j) is odd. Length 1 means position
  n-1 is alone, so a(n) = a(n-2) + 2; length 2 means a(n) = a(n-2) + 1.
- **Lean.** `SmallTrueThings/A156253.lean`.
  - A sequence defined by its runs is awkward to construct. Defining it by the recurrence being proved, then
    showing it has the run property (`run_spec`, strong induction), was short. Nested recursion needs a visible
    bound: `run (min (run (n+2)) (n+2))` with `decreasing_by all_goals omega`, and the `min` is removed afterwards.
  - "Position n lies in run k" as `S (k-1) < n ∧ n ≤ S k` with partial sums `S` makes every step an `omega` call.
  - `omega` treats `S K (0+1)`, `S K 1` and `S K (1-1)` as different atoms. State literal instances with a type
    ascription (`have hS1 : S K 1 = S K 0 + K 1 := S_succ K 0`) and close `1 - 1` goals with `simp`.
  - `if_pos`/`if_neg` are deprecated here: `ite_eq_left`/`ite_eq_right`.
  - To read a PDF linked from an entry: download it into its own folder under `scratch/` and run `pdftotext
    -layout`. The fetch tool could not read the PDF's text.

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

7. `git push`. The repository is public at https://github.com/linustalacko/small-true-things (Linus asked for
   that on 2026-11-20), so everything committed is read by strangers: no private paths, names or guesses stated as
   facts, and nothing about another project that was not checked.

Nothing goes to the OEIS without Linus, and nothing goes anywhere else public beyond this repository.

Since 2026-11-20 this runs once a day at about 1 pm, from the scheduled task `small-true-things-daily` in the Claude
desktop app. Each run starts with no memory, so whatever the next run needs to know goes in this file. An
unfinished day is an entry too.

## Things to know

- **Others are mining the same seam, by machine.** Found 2026-11-20: the GitHub project
  `the-omega-institute/trureturing` runs Claude Code and Codex agents over OEIS conjectures and proves them in Lean.
  It has about 1,300 issues with OEIS in the title, and it registered the A005121 conjecture on November 5, two weeks
  before the proof here (issue 27085, marked "Proved"). Sela Fried publishes a paper series of OEIS proofs. So:
  before starting a conjecture, search that repository for the A-number
  (`gh api "search/issues?q=repo:the-omega-institute/trureturing+A005121"`), search the web for the conjecture, and
  write in the README what was searched and found. Say "independent" unless priority has really been checked. If
  someone has it already, a different proof, or what the result means, can still be worth a page; a duplicate
  formal proof is not.

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

Seen in the harvests (`scratch/h_a.json`, `scratch/h_b.json`) and not settled on the entry as of 2026-11-20. My
guess at each is a guess, and none of these has been through all four checks yet.

| Entry | Conjecture | First look |
|---|---|---|
| A078008 | a(n) = number of fractions with even denominator in "the infinite Farey row of 2^n terms" (Adamson, 2003) | Not in trureturing as of 2026-11-20. Stern's diatomic sequence is even exactly at multiples of 3, which gives Jacobsthal-type counts, but the plain reading gives 0, 1, 1, 3, 5 and the sequence is 1, 0, 2, 2, 6: the row meant has to be pinned down from the HAKMEM link first |
| A154138 | Indices k with T(k) + 3 a square: conjectured g.f. (2009) | Not in trureturing. (2k+1)² − 8m² = −23, a Pell equation; needs the classes of solutions and a descent. A real one to formalize |
| A003278 | Szekeres's sequence in terms of A191107 and A055246 (Jeffery, 2015) | Not looked at; base 3 |
| A034836 | n = xyz with x ≤ y ≤ z: (np + 3·nsq + 2·ntp)/6 | Burnside, probably |
| A175254 | a(n) = Σ_k A006218(n−k) (Mathar, 2012) | As I read it, it fails at n = 2 (5 against 4). Read the entry properly before believing that |
| A056240 | a(n) = min of q · a(n−q) over certain primes q | Not looked at |

## Ruled out

Do not start these; each failed a novelty check.

| Entry | Why |
|---|---|
| A226857 | Barker's recurrence for numbers that are both a sum and a product of two Fibonacci numbers: proved by trureturing, September 2026 |
| A006068 | Kurkov's inverse Gray code recurrence: settled by trureturing |
| A145920 | Mathar's recurrence for pentagonal C(n,4): a corollary of a formula already on the entry (C(n,4) is pentagonal exactly when 3 does not divide n) |
| A129527 | a(n) = 2n − (odd part of n): the proof is sketched on the entry by Arndt |
| A034448 | Yanev's usigma formula: trureturing's screened-out file lists it; a one-line check on prime powers, and Fried proved its sibling on A001157 |

