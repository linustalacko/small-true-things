"""A040027 (Gould numbers), Yanev's conjecture (OEIS, Aug 31 2021): numerical checks.

  a(n) = Sum_{k=0..n} A058006(k) * Stirling2(n+1, k+1),
  A058006(k) = 0! - 1! + 2! - ... + (-1)^k k!.

1. The right side equals the Gould numbers from the entry's recurrence
   a(0) = 1, a(n) = Sum_{i=0..n-1} binomial(n, i+1) a(i)   (Jovovic 2001), for n up to N.
2. Both agree with the terms printed in the OEIS entry.
3. Brute force for small n: the recurrence counts the set partitions of {1..n+1}
   whose last block (blocks ordered by least element) is a singleton (Bala 2014).
4. The two Stirling identities the proof uses.
"""
import sys
from math import comb, factorial

N = int(sys.argv[1]) if len(sys.argv) > 1 else 300
BRUTE = int(sys.argv[2]) if len(sys.argv) > 2 else 9

OEIS = [1,1,3,9,31,121,523,2469,12611,69161,404663,2512769,16485691,113842301,
        824723643,6249805129,49416246911,406754704841,3478340425563,
        30845565317189,283187362333331,2687568043654521,26329932233283223]

S = [[0]*(N+3) for _ in range(N+3)]
S[0][0] = 1
for n in range(1, N+2):
    for k in range(1, n+1):
        S[n][k] = k*S[n-1][k] + S[n-1][k-1]

a = [1]
for n in range(1, N+1):
    a.append(sum(comb(n, i+1)*a[i] for i in range(n)))

c = [1]
for k in range(1, N+1):
    c.append(c[-1] + (-1)**k * factorial(k))

rhs = [sum(c[k]*S[n+1][k+1] for k in range(n+1)) for n in range(N+1)]
assert rhs == a, "conjecture fails"
assert a[:len(OEIS)] == OEIS, "does not match the OEIS data"
print(f"conjecture holds for 0 <= n <= {N}; first {len(OEIS)} terms match the OEIS")

def partitions(n):
    """Set partitions of {0..n-1} as lists of blocks, blocks in order of least element."""
    if n == 0:
        yield []
        return
    for p in partitions(n-1):
        for i in range(len(p)):
            yield p[:i] + [p[i] + [n-1]] + p[i+1:]
        yield p + [[n-1]]

for n in range(0, BRUTE+1):
    count = sum(1 for p in partitions(n+1) if len(p[-1]) == 1)
    assert count == a[n], (n, count, a[n])
print(f"a(n) counts partitions of an (n+1)-set with a singleton last block, n <= {BRUTE}")

M = min(N, 60)
for n in range(M):
    for m in range(n+2):
        assert S[n+1][m+1] == sum(comb(n, j)*S[j][m] for j in range(n+1))
    alt = sum((-1)**k * factorial(k) * S[n+1][k+1] for k in range(n+1))
    assert alt == (1 if n == 0 else 0)
print(f"both Stirling identities hold for n < {M}")
