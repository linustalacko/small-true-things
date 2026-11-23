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

## 2026-11-23: A056240, Sycamore and Marcus. Proved; no earlier proof found.

- **Novelty rechecked** before and after: still no trureturing issue or file, nothing on the web, nothing on the
  entry beyond a(n) ≥ n.
- **The odd case, which was open yesterday,** fell to two changes of view. (1) Yesterday's product bound
  (all parts < S/2 gives > S²/4) needed an induction with floors and exceptions. The form the proof actually uses is
  better: *integers ≥ 2, none above P, with sum P + r (r ≤ P, P ≥ 5), multiply to at least P·r.* Prove it by
  grouping, not induction: a list multiplies to at least the product of any grouping's sums. One part ≥ r gives two
  groups; otherwise add parts until the running sum first reaches r and cut there (two groups if that sum is ≤ P,
  three if not). Every inequality is then (x − a)(b − x) ≥ 0 in disguise. (2) In the odd case, split on "some odd
  factor w ≤ r" (rest sums to P + (r+3−w), apply the bound) against "all odd factors > r". In the second, one odd
  factor means at least four 2s, impossible because 3·5 < 2⁴ (the only place minimality is used beyond the
  definition), and three odd factors ≥ r + 2 force P ≥ 2r + 3, after which the three-group bound is loose.
- **Lean.** `SmallTrueThings/A056240.lean`, about 390 lines, compiled after six rounds of small fixes. Things that
  helped or hurt:
  - Prime factors as `Nat.primeFactorsList`, sopfr as its sum; `Nat.perm_primeFactorsList_mul` gives
    sopfr(ab) = sopfr a + sopfr b. Split the list into odd and even parts with `List.filter_append_perm`, defining the
    even part as `filter (fun x => !decide (x % 2 = 1))` so the lemma matches syntactically.
  - `zify` pushes casts *into* `List.sum` (`(List.map Nat.cast L).sum`), which omega then treats as a new atom.
    Put each polynomial inequality in its own lemma over plain naturals (`three_groups`, `three_large`) and zify there.
  - `set r := n - P` confused omega; `obtain ⟨r, hr⟩ : ∃ r, r = n - P := ⟨_, rfl⟩` did not.
  - After `match hOc : O with`, the name `O` is gone from the goals: no more `rw [hOc]`.
  - nlinarith proves cubic bounds if given the products as hints: substitute r = 4 + s, P = r + t mentally and pass
    `mul_nonneg` of the shifted variables, pairwise and triple.
  - Deprecations in this Mathlib: `push_neg` → `push Not`, `if_true` → `ite_true`, `Set.mem_setOf_eq` →
    `Set.mem_ofPred_eq`, `dif_pos` → `simp only [a0, h, dite_true]`.
- **Reusable.** `A056240.sum_le_prod` (lists of integers ≥ 2), `A056240.split` (first index where a running sum
  reaches r), `A056240.prod_ge_mul`. The grouping trick should settle other "smallest number with property of its
  factor multiset" conjectures.

## 2026-11-22: screening day; A056240 started, not finished

No result today. Seven candidates ruled out (table below), and one that passes every check is under way.

- **Ruled out, with what settled each.** A000139 (Bala 2025: the 2-stack-sortable count is odd exactly on
  A022341). This was the best of the day and is already a theorem: the 2005 Permutation Patterns problem list
  (arXiv math/0505504, Bóna's problem) states it and cites a combinatorial proof by Bóna. The 2-adic proof
  is short too: v2 a(n) = v2 C(3n,n) + 1 - v2(n+1), and by Kummer v2 C(3n,n) counts the carries in n + 2n.
  An OEIS comment pointing to Bóna would be worth Linus's time. A000384 (Chu's hexagonal sumset):
  trureturing issue 26346, November 4, with the same endpoint-block construction I had found. A002464, A122946:
  proofs on the entries. A001008 (Bala's harmonic identity for all m): Niu, arXiv:2604.23206. A034836: the
  entry cites the formula as eq. 11 of Andrica and Ionascu 2013. A175254: false as printed (n = 2 gives 5
  against 4), almost certainly a typo for the partial-sum fact already on the entry.
- **Screening method that saved time.** One `gh api search/issues` call per A-number, 2.2 s apart, over all 158
  conjecture-bearing entries in the five harvests (`scratch/tr_hits.txt`, 47 hits). Do this before reading
  anything; it caught A000384 only after I had a proof.
- **A056240, the candidate.** a(n) is the smallest number whose prime factors add up to n. Sycamore and Marcus
  (2017) conjecture a(n) = min{q·a(n−q) : q prime, P_n ≤ q < n−1}, where P_n is the largest Goldbach-type prime
  (n − P_n prime for even n, n − 3 − P_n prime for odd n), n composite and not 6. In words: the cheapest number
  with prime-sum n spends almost all of n on one large prime. Novelty: nothing on the entry, A288814 or
  A288313; no trureturing issue or file for A056240 or A064364; a web search found nothing. Checked to n = 20000
  (`A056240/check.py`). The conjecture assumes nothing about Goldbach; it is stated for the n where P_n exists.
- **Proof so far, on paper.** (1) Optimal substructure: any prime q dividing a(n) has a(n) = q·a(n−q), so the
  conjecture is equivalent to "the largest prime factor Q of a(n) is at least P_n" (checked to 5000). (2) Basic
  bound: integers ≥ 2 with sum S and largest x have product ≥ x(S−x). (3) Product bound: if every part is below
  S/2, the product is ≥ ⌊S²/4⌋, and > S²/4 for S ≥ 9 (checked S ≤ 120; the one failure of the weak form is
  {2,2,2}, which is why n = 6 is excluded). Proof sketch by induction on the number of parts: take the largest
  x and the rest Y of sum r; if Y's largest part is at most r/2 use the induction, else Y ≥ 2(r−2) by (2); both
  close for r ≥ 5, with small r by enumeration. (4) **Even n is then done**: P ≥ n/2 (else its partner is a
  larger candidate) and a(n) ≤ P(n−P). If Q < P: when 2Q ≥ n, a(n) ≥ Q(n−Q) > P(n−P); when 2Q < n, (3) gives
  a(n) > n²/4 ≥ P(n−P) for n ≥ 9; n = 8 by hand. (5) **Odd n is not done.** Here a(n) ≤ 3·P·r with
  P + r = n − 3, P ≥ r, and a(n) has at least three prime factors (two would force 2 + (n−2) and Q = n−2 ≥ P).
  If 3 divides a(n), apply (2)/(3) to the rest with t = P and multiply by 3: done for n ≥ 12. If not, take the
  smallest odd factor w ≥ 5: done when w ≤ r, using (w−3)(r−w) ≥ 0. Open: w > r + 1 (then all odd factors are
  large, so r is small and the bound C is close to linear in n; a single odd factor, a(n) = 2^k·u, goes through by a direct
  estimate because P > u forces r < 2k − 3; three or more large odd factors is the case left).
- **Next run.** Finish the odd case on paper first, then Lean. Plan for Lean: state over any `a` with
  `sopfr (a n) = n` and minimality as hypotheses, sopfr as `(Nat.primeFactorsList m).sum`, and prove (2) and (3)
  for `List ℕ` by induction before touching primes. Small n (≤ 12) by `decide` on explicit factorizations.

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

Seen in the harvests (`scratch/h_a.json` to `scratch/h_e.json`; trureturing hit counts for all of them in
`scratch/tr_hits.txt`, 2026-11-22) and not settled on the entry as of 2026-11-20. My
guess at each is a guess, and none of these has been through all four checks yet.

| Entry | Conjecture | First look |
|---|---|---|
| A078008 | a(n) = number of fractions with even denominator in "the infinite Farey row of 2^n terms" (Adamson, 2003) | Not in trureturing as of 2026-11-20. Stern's diatomic sequence is even exactly at multiples of 3, which gives Jacobsthal-type counts, but the plain reading gives 0, 1, 1, 3, 5 and the sequence is 1, 0, 2, 2, 6: the row meant has to be pinned down from the HAKMEM link first |
| A154138 | Indices k with T(k) + 3 a square: conjectured g.f. (2009) | Not in trureturing. (2k+1)² − 8m² = −23, a Pell equation; needs the classes of solutions and a descent. A real one to formalize. 2026-11-22: Seidov writes he believes it; the cited SeqFan thread is not archived, so whether Adams-Watters proved it there is unknown |
| A003278 | Szekeres's sequence in terms of A191107 and A055246 (Jeffery, 2015) | Not looked at; base 3 |
| A098557 | Mathar's recurrence for the e.g.f. (1+x)·log((1+x)/(1−x))/2 | Not screened; D-finite, likely routine, low beauty |
| A284230 | Mathar's recurrence for self-avoiding walks in a strip | Not screened; needs the walks' own transfer matrix |
| A338024 | Cyclic four-peg Hanoi: a(n) = a(n−1) + a(n−2) + a(n−3) − 2a(n−5) for n > 11 | Not screened; looks hard, would need an optimal-strategy theorem |
| A383424, A383426 | Gap sets of index sequences built on the Fibonacci word A003849 | Not screened; Walnut-style automatic sequences, Dekking has settled siblings (A285683) |

## Ruled out

Do not start these; each failed a novelty check.

| Entry | Why |
|---|---|
| A226857 | Barker's recurrence for numbers that are both a sum and a product of two Fibonacci numbers: proved by trureturing, September 2026 |
| A006068 | Kurkov's inverse Gray code recurrence: settled by trureturing |
| A145920 | Mathar's recurrence for pentagonal C(n,4): a corollary of a formula already on the entry (C(n,4) is pentagonal exactly when 3 does not divide n) |
| A129527 | a(n) = 2n − (odd part of n): the proof is sketched on the entry by Arndt |
| A034448 | Yanev's usigma formula: trureturing's screened-out file lists it; a one-line check on prime powers, and Fried proved its sibling on A001157 |
| A000139 | Bala's parity conjecture (odd iff n in A022341): stated as known in the 2005 Permutation Patterns problem list (arXiv math/0505504), with a combinatorial proof by Bóna |
| A000384 | Chu's hexagonal sumset minimum: trureturing issue 26346 (2026-11-04) |
| A002464 | Keith's Stirling-type formula for Hertzsprung's problem: proof on the entry |
| A122946 | Meeussen's even Markov numbers per generation: proof on the entry |
| A001008 | Bala's general-m harmonic identity: Niu, arXiv:2604.23206 |
| A034836 | Boxes of volume n by Burnside: the entry cites the same formula as eq. 11 of Andrica and Ionascu (2013) |
| A175254 | Mathar's Σ A006218(n−k): false as printed (n = 2: 5 against 4), a typo for the partial-sum fact on the entry |
| A000051 | Luschny's permanent conjecture: proved in Fried's note, per the entry |
| A000700, A010815 | Plouffe's e^(−π) evaluations: proofs on the entries (class invariant, pentagonal theorem) |

