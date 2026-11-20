"""A156253 (run index of the Kolakoski sequence), Maiga's conjecture (OEIS, Dec 09 2021):

  a(n) = (a(a(n-1)) mod 2) + a(n-2) + 1.

A156253(n) is the least k with A054353(k) >= n, where A054353 are the partial sums of
the Kolakoski sequence A000002: the number of the run that position n lies in.

1. Build the Kolakoski sequence from its definition and check the conjecture for 3 <= n <= N.
2. Check the sibling recurrence a(n) = a(n - gcd(a(a(n-1)), 2)) + 1 (Maiga 2023) as well.
3. Compare with the terms printed in the OEIS entries.
4. Run the recurrence alone from a(1) = 1, a(2) = 2 and check it rebuilds the sequence:
   K(n) = 1 if a(n) is odd, 2 if even.
"""
import sys
from math import gcd

N = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000

OEIS_A156253 = [1,2,2,3,3,4,5,6,6,7,8,8,9,9,10,11,11,12,12,13,14,15,15,16,17,18,18,19,19,
                20,21,21,22,23,24,24,25,26,26,27,27,28,29,30,30,31,32,33,33,34,35,35,36,36]
OEIS_A000002 = [1,2,2,1,1,2,1,2,2,1,2,2,1,1,2,1,1,2,2,1,2,1,1,2,1,2,2,1,1,2,1,1,2,1,2,2,1,2,2,1,1]

# Kolakoski from its definition: the k-th run has length K(k), runs alternate 1, 2, 1, 2, ...
K = [0, 1, 2, 2]              # 1-indexed
k = 3                         # next run to write
while len(K) <= N + 2:
    K.extend([1 if k % 2 == 1 else 2] * K[k])
    k += 1
assert K[1:len(OEIS_A000002)+1] == OEIS_A000002

# a(n) = number of the run containing position n
a = [0] * (N + 1)
run, pos = 0, 0
while pos < N:
    run += 1
    for _ in range(K[run]):
        pos += 1
        if pos <= N:
            a[pos] = run
assert a[1:len(OEIS_A156253)+1] == OEIS_A156253

for n in range(3, N + 1):
    assert a[n] == a[a[n-1]] % 2 + a[n-2] + 1, n
    assert a[n] == a[n - gcd(a[a[n-1]], 2)] + 1, n
print(f"both recurrences hold for 3 <= n <= {N}; the first terms match the OEIS")

b = [0, 1, 2] + [0] * (N - 2)
for n in range(3, N + 1):
    b[n] = b[b[n-1]] % 2 + b[n-2] + 1
assert b == a
assert all(K[n] == (1 if b[n] % 2 == 1 else 2) for n in range(1, N + 1))
print(f"the recurrence alone rebuilds the Kolakoski sequence for n <= {N}")
