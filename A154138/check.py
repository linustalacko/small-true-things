"""A154138, numbers k with 3 + k(k+1)/2 a square: Mathar's conjectures (OEIS, Oct 18 2009).

  a(n) = a(n-1) + 6a(n-2) - 6a(n-3) - a(n-4) + a(n-5),
  G.f. x(1 + 2x + 3x^2 - 2x^3 - 2x^4) / ((1-x)(x^2-2x-1)(x^2+2x-1)),
  and Seidov's form a(1..4) = 1, 3, 12, 22, a(n) = 6a(n-2) - a(n-4) + 2.

1. Brute force: every k <= LIMIT with 3 + k(k+1)/2 square, against the recurrence.
2. Far out: 400 terms of the recurrence are all in the set, and between consecutive terms
   there is no other solution, by listing every solution of x^2 + 23 = 8y^2 (x = 2k+1)
   with y below a bound through y itself (each y tested with isqrt, not with the descent).
3. The generating function's first 400 coefficients equal the recurrence's terms.
4. The descent the proof uses: (x, y) -> (3x - 8y, 3y - x) maps solutions with y >= 6 to
   solutions with a smaller positive y, ending at (3, 2) or (7, 3).
"""
import sys
from math import isqrt

LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 3 * 10**7
YMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 2 * 10**8

OEIS = [1, 3, 12, 22, 73, 131, 428, 766, 2497, 4467, 14556, 26038, 84841, 151763, 494492, 884542,
        2882113, 5155491, 16798188, 30048406, 97907017, 175134947, 570643916, 1020761278,
        3325956481, 5949432723, 19385094972, 34675835062, 112984613353]

def in_set(k):
    t = 3 + k * (k + 1) // 2
    r = isqrt(t)
    return r * r == t

a = [1, 3, 12, 22]
while len(a) < 400:
    a.append(6 * a[-2] - a[-4] + 2)
assert a[:len(OEIS)] == OEIS
b = a[:5]
while len(b) < 400:
    b.append(b[-1] + 6 * b[-2] - 6 * b[-3] - b[-4] + b[-5])
assert b == a, "Mathar's five-term recurrence and Seidov's form differ"

# 1. brute force
found = [k for k in range(LIMIT + 1) if in_set(k)]
assert found == [x for x in a if x <= LIMIT], found[:20]
print(f"brute force: the {len(found)} k <= {LIMIT} are exactly the recurrence's terms")

# 2. all terms are in the set; every solution with y <= YMAX is a term
assert all(in_set(x) for x in a)
sols = []
for y in range(1, YMAX + 1):
    t = 8 * y * y - 23
    if t > 0:
        x = isqrt(t)
        if x * x == t:
            sols.append((x - 1) // 2)
assert sols == [x for x in a if 3 + x * (x + 1) // 2 <= YMAX * YMAX], sols[:20]
print(f"400 terms all qualify (largest has {len(str(a[-1]))} digits); "
      f"every solution with y <= {YMAX} ({len(sols)} of them) is a term")

# 3. generating function
num = [0, 1, 2, 3, -2, -2]
den = [1, -1, -6, 6, 1, -1]   # (1-x)(x^2-2x-1)(x^2+2x-1) = (1-x)(1 - 6x^2 + x^4)
c = []
for n in range(401):
    s = num[n] if n < len(num) else 0
    s -= sum(den[j] * c[n - j] for j in range(1, min(n, 5) + 1))
    c.append(s)
assert c[0] == 0 and c[1:] == a
print("the generating function's coefficients 1..400 are the terms")

# 4. descent
for x, y in [(2 * k + 1, isqrt(3 + k * (k + 1) // 2)) for k in a[:60]]:
    path = [(x, y)]
    while y >= 6:
        x, y = 3 * x - 8 * y, 3 * y - x
        assert x > 0 and 0 < y < path[-1][1] and x * x + 23 == 8 * y * y
        path.append((x, y))
    assert (x, y) in [(3, 2), (7, 3)], path
print("descent from the first 60 solutions ends at (3, 2) or (7, 3)")
