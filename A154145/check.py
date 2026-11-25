"""A154145, numbers k with 15 + k(k+1)/2 a square: Mathar's conjectures (OEIS, Oct 18 2009),

  a(n) = a(n-1) + 6a(n-4) - 6a(n-5) - a(n-8) + a(n-9),
  G.f. x(-1-3x-2x^2-5x^3-3x^4+5x^5+2x^6+3x^7+2x^8) / ((x-1)(x^4+2x^2-1)(x^4-2x^2-1)),

against Zizka's comment a(1..4) = 1, 4, 6, 11, a(n) = 6a(n-2) - a(n-4) + 2, which is false.

1. Brute force: every k <= LIMIT with 15 + k(k+1)/2 square, against the recurrence.
2. Far out: 400 terms of the recurrence are all in the set, and every solution of
   x^2 + 119 = 8y^2 (x = 2k+1) with y <= YMAX, found by testing each y with isqrt, is a term.
3. The generating function's first 400 coefficients equal the recurrence's terms.
4. The descent the proof uses: (x, y) -> (3x - 8y, 3y - x) maps solutions with y >= 12 to
   solutions with a smaller y, ending at one of (3, 4), (9, 5), (13, 6), (23, 9).
5. Zizka's two-step form fails first at n = 5 (and at every n from 5 to 400).
"""
import sys
from math import isqrt

LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 3 * 10**7
YMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 2 * 10**8

OEIS = [1, 4, 6, 11, 20, 33, 43, 70, 121, 196, 254, 411, 708, 1145, 1483, 2398, 4129, 6676,
        8646, 13979, 24068, 38913, 50395, 81478, 140281, 226804, 293726, 474891, 817620,
        1321913, 1711963, 2767870, 4765441, 7704676, 9978054, 16132331, 27775028]

def in_set(k):
    t = 15 + k * (k + 1) // 2
    r = isqrt(t)
    return r * r == t

# the four-chain form proved here: a(n) = 6a(n-4) - a(n-8) + 2 for n > 8
a = [1, 4, 6, 11, 20, 33, 43, 70]
while len(a) < 400:
    a.append(6 * a[-4] - a[-8] + 2)
assert a[:len(OEIS)] == OEIS
b = a[:9]
while len(b) < 400:
    b.append(b[-1] + 6 * b[-4] - 6 * b[-5] - b[-8] + b[-9])
assert b == a, "Mathar's recurrence and the four-chain form differ"

# 1. brute force
found = [k for k in range(LIMIT + 1) if in_set(k)]
assert found == [x for x in a if x <= LIMIT], found[:20]
print(f"brute force: the {len(found)} k <= {LIMIT} are exactly the recurrence's terms")

# 2. all terms are in the set; every solution with y <= YMAX is a term
assert all(in_set(x) for x in a)
sols = []
for y in range(1, YMAX + 1):
    t = 8 * y * y - 119
    if t > 0:
        x = isqrt(t)
        if x * x == t:
            sols.append((x - 1) // 2)
assert sols == [x for x in a if 15 + x * (x + 1) // 2 <= YMAX * YMAX], sols[:20]
print(f"400 terms all qualify (largest has {len(str(a[-1]))} digits); "
      f"every solution with y <= {YMAX} ({len(sols)} of them) is a term")

# 3. generating function: den * A = num, den = (x-1)(x^8 - 6x^4 + 1)
num = [0, -1, -3, -2, -5, -3, 5, 2, 3, 2]
den = [-1, 1, 0, 0, 6, -6, 0, 0, -1, 1]
p1 = [-1, 1]; p2 = [-1, 0, 2, 0, 1]; p3 = [-1, 0, -2, 0, 1]
def mul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, u in enumerate(p):
        for j, v in enumerate(q):
            r[i + j] += u * v
    return r
assert mul(mul(p1, p2), p3) == den
c = []
for n in range(401):
    s = num[n] if n < len(num) else 0
    s -= sum(den[j] * c[n - j] for j in range(1, min(n, 9) + 1))
    c.append(s // den[0])
assert c[0] == 0 and c[1:] == a
print("the generating function's coefficients 1..400 are the terms")

# 4. descent
bases = [(3, 4), (9, 5), (13, 6), (23, 9)]
assert [(x, y) for y in range(1, 12) for x in range(1, 3 * y + 1) if x * x + 119 == 8 * y * y] == bases
for x, y in [(2 * k + 1, isqrt(15 + k * (k + 1) // 2)) for k in a[:80]]:
    path = [(x, y)]
    while y >= 12:
        x, y = 3 * x - 8 * y, 3 * y - x
        assert x > 0 and 0 < y < path[-1][1] and x * x + 119 == 8 * y * y
        path.append((x, y))
    assert (x, y) in bases, path
print("descent from the first 80 solutions ends at (3, 4), (9, 5), (13, 6) or (23, 9)")

# 5. Zizka's form
bad = [n for n in range(5, 401) if a[n - 1] != 6 * a[n - 3] - a[n - 5] + 2]
assert bad[0] == 5 and bad == list(range(5, 401))
print(f"Zizka's a(n) = 6a(n-2) - a(n-4) + 2 fails at n = 5: a(5) = {a[4]}, "
      f"formula gives {6 * a[2] - a[0] + 2}; it fails at every n from 5 to 400")
