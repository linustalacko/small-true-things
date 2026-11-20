"""A005121, Mohapatra's conjecture (OEIS, Oct 30 2026): numerical checks.

1. R(n,n) from the conjectured triangle equals Lengyel's recurrence
   a(n) = Sum_{k=1..n-1} Stirling2(n,k) a(k), for n up to N.
2. Both agree with the terms printed in the OEIS entry.
3. Brute force for small n: R(n,k) counts the chains from bottom to top of the
   partition lattice of {1..n} whose finest non-trivial partition has k+1 as
   its smallest element that is not the least of its block.
"""
import sys
from functools import lru_cache
from collections import Counter

N = int(sys.argv[1]) if len(sys.argv) > 1 else 150
BRUTE = int(sys.argv[2]) if len(sys.argv) > 2 else 7

OEIS = [1,1,4,32,436,9012,262760,10270696,518277560,32795928016,2542945605432,
        237106822506952,26173354092593696,3375693096567983232,
        502995942483693043200,85750135569136650473360,
        16583651916595710735271248,3611157196483089769387182064,
        879518067472225603327860638128]

# Stirling numbers of the second kind
S = [[0]*(N+2) for _ in range(N+2)]
S[0][0] = 1
for n in range(1, N+1):
    for k in range(1, n+1):
        S[n][k] = k*S[n-1][k] + S[n-1][k-1]

# Lengyel's recurrence
a = [0]*(N+1); a[1] = 1
for n in range(2, N+1):
    a[n] = sum(S[n][k]*a[k] for k in range(1, n))

# the conjectured triangle
R = [[0]*(N+2) for _ in range(N+2)]
R[1][1] = 1
for n in range(2, N+1):
    for k in range(1, n):
        R[n][k] = k*sum(R[n-1][j] for j in range(k, n))
    R[n][n] = sum(R[n][j] for j in range(1, n))

assert all(R[n][n] == a[n] for n in range(1, N+1)), "conjecture fails"
assert a[1:len(OEIS)+1] == OEIS, "does not match the OEIS data"
print(f"R(n,n) = a(n) for 1 <= n <= {N}; first {len(OEIS)} terms match the OEIS")

# brute force: chains in the partition lattice, by the statistic of the first step
def partitions(blocks):
    """All set partitions of a list of items, as tuples of tuples."""
    if not blocks:
        yield ()
        return
    first, rest = blocks[0], blocks[1:]
    for p in partitions(rest):
        yield ((first,),) + p
        for i in range(len(p)):
            yield p[:i] + ((first,) + p[i],) + p[i+1:]

@lru_cache(None)
def chains(m):
    """Chains from bottom to top of the partition lattice of an m-set."""
    if m == 1:
        return 1
    return sum(chains(len(p)) for p in partitions(list(range(m))) if len(p) < m)

def statistic(p):
    """Smallest element (1-based) that is not the least of its block, minus 1."""
    mins = {min(b) for b in p}
    n = sum(len(b) for b in p)
    return min(x for x in range(n) if x not in mins)  # 0-based x = (x+1) - 1

for n in range(2, BRUTE+1):
    count = Counter()
    for p in partitions(list(range(n))):
        if len(p) < n:
            count[statistic(p)] += chains(len(p))
    row = [count[k] for k in range(1, n)]
    assert row == R[n][1:n], (n, row, R[n][1:n])
    assert sum(row) == a[n]
    print(f"n={n}: chains by statistic {row}  = R({n},1..{n-1})")
