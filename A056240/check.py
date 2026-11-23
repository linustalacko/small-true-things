"""A056240: a(n) = smallest number whose prime factors, with multiplicity, sum to n.

Conjecture on the entry (Sycamore and Marcus, 2017): for composite n other than 6,
    a(n) = min { q * a(n-q) : q prime, P_n <= q < n-1 },
where P_n is the largest prime below n-1 with n - P_n prime (n even), or with n-3-P_n prime (n odd).

This script checks the conjecture, and the equivalent form used in the proof (the largest
prime factor of a(n) is at least P_n), for every composite n up to N. It also checks the
product bound the proof rests on.

Run: python3 A056240/check.py [N]   (default 20000, a few seconds)
"""
import sys
from functools import lru_cache

N = int(sys.argv[1]) if len(sys.argv) > 1 else 20000

is_prime = bytearray([1]) * (N + 1)
is_prime[0] = is_prime[1] = 0
for i in range(2, int(N ** 0.5) + 1):
    if is_prime[i]:
        is_prime[i * i :: i] = bytearray(len(is_prime[i * i :: i]))
primes = [p for p in range(2, N + 1) if is_prime[p]]

# a[n] by the exact recursion a(n) = min over primes q of q * a(n-q), with a(0) = 1.
INF = float("inf")
a = [INF] * (N + 1)
a[0] = 1
for n in range(2, N + 1):
    best = INF
    for q in primes:
        if q > n:
            break
        if n - q != 1:
            best = min(best, q * a[n - q])
    a[n] = best


def largest_prime_factor(m):
    f, p = 1, 2
    while p * p <= m:
        while m % p == 0:
            f, m = p, m // p
        p += 1
    return max(f, m) if m > 1 else f


failures = 0
for n in range(4, N + 1):
    if is_prime[n] or n == 6:
        continue
    if n % 2 == 0:
        P = next(p for p in range(n - 2, 1, -1) if is_prime[p] and is_prime[n - p])
    else:
        P = next(p for p in range(n - 2, 1, -1) if is_prime[p] and n - 3 - p >= 2 and is_prime[n - 3 - p])
    rhs = min(q * a[n - q] for q in primes if P <= q < n - 1)
    if rhs != a[n]:
        failures += 1
        print("conjecture fails at", n, P, a[n], rhs)
    if n <= 5000 and largest_prime_factor(a[n]) < P:
        failures += 1
        print("equivalent form fails at", n)
print(f"conjecture: composite n = 4..{N}, n != 6, failures: {failures}")


# The product bound the proof rests on (`prod_ge_mul` in the Lean file): integers >= 2,
# none above P, with sum P + r where r <= P and P >= 5, multiply to at least P * r.
# For P = r = 3 it fails ({2,2,2}: 8 < 9), which is why the entry excludes n = 6.
@lru_cache(None)
def min_product(S, cap):
    if S == 0:
        return 1
    best = INF
    for x in range(2, min(cap, S) + 1):
        if S - x != 1:
            best = min(best, x * min_product(S - x, x))
    return best


for S in range(5, 161):
    for P in range(5, S + 1):
        r = S - P
        if r <= P:
            assert min_product(S, P) >= P * r, (S, P)
assert min_product(6, 3) == 8
print("product bound: checked P + r = 5..160")
