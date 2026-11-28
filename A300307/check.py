"""A300307: a(n) = number of sign choices with 1 +- 3 +- 6 +- ... +- n(n+1)/2 == 0 (mod n).
Checks Manyama's conjecture a(2^m) = 2^(2^m - m) for m >= 1, and the lemma the proof rests on."""
import itertools, sys

def a(n):
    """Count by dynamic programming over residues mod n. The first sign is +."""
    cnt = [0] * n
    cnt[1 % n] = 1
    for k in range(2, n + 1):
        t = k * (k + 1) // 2 % n
        cnt = [cnt[(r - t) % n] + cnt[(r + t) % n] for r in range(n)]
    return cnt[0]

# Against the first terms printed on the entry (%S line).
DATA = [1, 2, 0, 4, 4, 16, 12, 32, 20, 112, 88, 384, 308, 1264, 1056, 4096, 3852, 15120, 13820]
assert [a(n) for n in range(1, len(DATA) + 1)] == DATA

M = int(sys.argv[1]) if len(sys.argv) > 1 else 12
for m in range(1, M + 1):
    n = 2 ** m
    assert a(n) == 2 ** (n - m), (m, a(n))
print(f"a(2^m) = 2^(2^m - m) for m = 1..{M} (n up to {2 ** M})")
print("m = 0 is excluded on the entry: a(1) = 1, not 2")

# The lemma: if x_j = 2^j * odd for j = 0..M-1 occur in a list, its subset sums are uniform mod 2^M.
def uniform(xs, M):
    c = [0] * 2 ** M
    for S in itertools.product([0, 1], repeat=len(xs)):
        c[sum(x for x, s in zip(xs, S) if s) % 2 ** M] += 1
    return len(set(c)) == 1
import random
random.seed(1)
for _ in range(300):
    M2 = random.randint(1, 4)
    xs = [2 ** j * random.randrange(1, 40, 2) for j in range(M2)] + [random.randrange(100) for _ in range(random.randint(0, 4))]
    random.shuffle(xs)
    assert uniform(xs, M2)
print("lemma: 300 random lists, subset sums uniform")
