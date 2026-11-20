# A005121: Mohapatra's triangle for the chains of the partition lattice

**Status: proved, and checked by Lean** (`SmallTrueThings/A005121.lean`, theorem `A005121.mohapatra`). November 20 2026.

## The conjecture

[A005121](https://oeis.org/A005121) is 1, 1, 4, 32, 436, 9012, 262760, …: the number of chains from the bottom
(all singletons) to the top (one block) of the lattice of set partitions of {1, …, n}. Its established formula is
Lengyel's recurrence

> a(1) = 1, a(n) = Σ_{k=1..n-1} S(n,k) · a(k),

where S(n,k) is the Stirling number of the second kind: choose the finest partition of the chain other than the
bottom, with k < n blocks, then a chain on those k blocks.

The entry carries this comment by Rajesh Kumar Mohapatra, dated October 30 2026:

> Conjecture: a(n) = R(n,n) where R(1,1) = 1, R(n,k) = k · Σ_{j=k..n-1} R(n-1,j) for 1 ≤ k < n,
> R(n,n) = Σ_{j=1..n-1} R(n,j).

The triangle begins

```
1
1    1
2    2    4
8   12   12   32
64  112  132  128  436
872 1616 2088 2256 2180 9012
```

## The proof

Write h_d(k, …, m) for the sum, over all multisets of d integers taken from k, k+1, …, m, of the product of the
multiset (the complete homogeneous symmetric polynomial; h_0 = 1). Two facts about it:

1. **Sorting by the least element.** A multiset of d+1 integers from k, …, m is its least element j and a multiset
   of d integers from j, …, m. So h_{d+1}(k, …, m) = Σ_{j=k..m} j · h_d(j, …, m).
2. **Stirling numbers.** S(m+d, m) = h_d(1, …, m). (Both obey the same recurrence: a multiset from 1, …, m+1
   either contains m+1 or does not.)

**Lemma.** For 1 ≤ k ≤ n,

> R(n+1, k) = Σ_{m=k..n} a'(m) · k · h_{n-m}(k, …, m), where a'(m) = R(m,m).

*Proof.* Induction on n. The rule gives R(n+1,k) = k · (R(n,n) + Σ_{j=k..n-1} R(n,j)). The first term is the
m = n term of the claim. In the second, expand each R(n,j) by the induction hypothesis and swap the two sums:

> k · Σ_{m=k..n-1} a'(m) · Σ_{j=k..m} j · h_{n-1-m}(j, …, m) = k · Σ_{m=k..n-1} a'(m) · h_{n-m}(k, …, m)

by fact 1. ∎

**Theorem.** R(n,n) = a(n) for all n ≥ 1.

*Proof.* Sum the lemma over k and swap the sums:

> R(n+1,n+1) = Σ_{k=1..n} R(n+1,k) = Σ_{m=1..n} a'(m) · Σ_{k=1..m} k · h_{n-m}(k, …, m)
> = Σ_{m=1..n} a'(m) · h_{n-m+1}(1, …, m) = Σ_{m=1..n} S(n+1, m) · a'(m),

using fact 1 and then fact 2. So the diagonal obeys Lengyel's recurrence, and it starts at R(1,1) = 1 = a(1). ∎

## What the triangle counts

The proof also says what the entries below the diagonal are.

**Corollary.** For 1 ≤ k < n, R(n,k) is the number of chains from bottom to top whose finest partition other than
the bottom has 1, …, k in k different blocks and k+1 in a block with one of them.

*Why.* Build a partition of {1, …, n} into m blocks by adding 1, 2, …, n in turn; each element opens a new block or
joins one of the b blocks already there, in b ways. If 1, …, k open blocks and k+1 joins one (k ways), the n-m-1
later joiners see block counts that are weakly increasing and lie between k and m, and every such sequence happens
exactly once. So there are k · h_{n-m-1}(k, …, m) such partitions, and each is followed by one of a(m) chains: that
is the lemma.

Every chain has exactly one such k, which is the rule R(n,n) = Σ_{j<n} R(n,j).

The corollary is proved on paper and checked by brute force for n ≤ 8 (`check.py`); it is not in the Lean file.

## What was checked, and how

| Check | Result |
|---|---|
| `python3 A005121/check.py 150 8` | R(n,n) = a(n) for n ≤ 150; the first 19 terms match the OEIS; the corollary holds for n ≤ 8 by listing every partition |
| `lake build` | `A005121.mohapatra` compiles; `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` |

The Lean theorem takes any `R` and `a` and assumes exactly the conjecture's three rules and Lengyel's recurrence,
with `Nat.stirlingSecond` from Mathlib, so there are no definitions of mine to trust in its statement. `T` and `L` in
the same file are a triangle and a sequence that obey the rules, which shows the rules do not contradict each other.

What Lean does not check: that Lengyel's recurrence counts the chains. That is the entry's own formula (Lengyel
1984), and the brute-force count agrees with it for n ≤ 8.

## Not the first

Found after the proof was written, when Linus asked whether anyone else had proved it. An automated proving project,
[the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing/issues/27085), registered this
same conjecture as a target on November 5 2026, two weeks before this proof, with the same reading of it (any `R` and
`a` obeying the printed rules, Mathlib's `Nat.stirlingSecond`). The issue's title is marked "Proved". Their Lean file
was not found on the repository's default branch, so their proof is unverified from here, but this proof should be
called independent, not first. Their issue says it claims no combinatorial meaning for the triangle, so the corollary
above may be the only part that is new; that was not checked either.

## Not done

Nothing has been sent to the OEIS. A comment for the entry, if Linus wants to send one (check the entry and the
project above first; a proof may be posted there already):

> Mohapatra's conjecture is true. For 1 <= k < n, R(n,k) = Sum_{m=k..n-1} a(m)*k*h_{n-m-1}(k,...,m), where h_d is
> the complete homogeneous symmetric polynomial of degree d; summing over k, with
> Sum_{k=1..m} k*h_{d-1}(k,...,m) = h_d(1,...,m) = Stirling2(m+d,m), gives Lengyel's recurrence. R(n,k) is the
> number of chains whose finest partition other than the minimum has 1..k in distinct blocks and k+1 in a block
> with one of them. The proof was found by an AI (Claude) and is formalized in Lean 4.
