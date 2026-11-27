"""The family {k : c + k(k+1)/2 is a square} (A001108, A006451, A154138 to A154154, A175032).

The theorem proved here: with x = 2k+1 and N = 8c - 1, the condition is x^2 + N = 8y^2. Call a
solution small when x^2 < 8N, and let m be the number of small solutions. Then the members of the
set, in increasing order a(0) < a(1) < ..., satisfy a(n+m) = T(a(n)), where T(k) = 3k + 1 + 4y
(the unit 3 + sqrt 8 acting on (x, y)), and so a(n+2m) = 6a(n+m) - a(n) + 2.

1. For every c from 1 to CMAX, the members up to LIMIT found by brute force obey a(n+m) = T(a(n)).
2. The small solutions are exactly the ones not of the form T(k): checked for each c.
3. For the eight entries whose formulas are still marked as conjectures (c = 8, 10, 13, 21, 24,
   25, 28, 30), m = 2, the printed terms agree, and the printed recurrence and g.f. agree with
   400 terms of a(n) = 6a(n-2) - a(n-4) + 2.
"""
import sys
from math import isqrt

CMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 300
LIMIT = int(sys.argv[2]) if len(sys.argv) > 2 else 2 * 10**6

def square_y(c, k):
    t = c + k * (k + 1) // 2
    r = isqrt(t)
    return r if r * r == t else None

def T(c, k):
    return 3 * k + 1 + 4 * square_y(c, k)

def small(c, k):
    return (2 * k + 1) ** 2 < 8 * (8 * c - 1)

# 1 and 2
chains = {}
for c in range(1, CMAX + 1):
    members = [k for k in range(LIMIT + 1) if square_y(c, k) is not None]
    m = sum(1 for k in members if small(c, k))
    assert all(small(c, k) for k in members[:m]) and not any(small(c, k) for k in members[m:])
    for n in range(len(members) - m):
        assert members[n + m] == T(c, members[n]), (c, n)
    images = {T(c, k) for k in members}
    assert [k for k in members if k not in images] == members[:m], c
    chains[c] = m
counts = sorted(set(chains.values()))
print(f"c = 1..{CMAX}: members up to {LIMIT} obey a(n+m) = T(a(n)); m takes the values {counts}; "
      f"the small members are exactly those not of the form T(k)")

# 3
ENTRIES = {
    "A154141": (8, [1, 7, 16, 46, 97, 271, 568, 1582, 3313, 9223, 19312, 53758, 112561, 313327, 656056, 1826206, 3823777, 10643911, 22286608, 62037262, 129895873, 361579663, 757088632, 2107440718, 4412635921, 12283064647, 25718726896, 71590947166, 149899725457, 417262618351],
                [1, 6, 3, -6, -2], -1),
    "A154143": (10, [3, 5, 26, 36, 155, 213, 906, 1244, 5283, 7253, 30794, 42276, 179483, 246405, 1046106, 1436156, 6097155, 8370533, 35536826, 48787044, 207123803, 284351733, 1207205994, 1657323356, 7036112163, 9659588405, 41009466986, 56300207076, 239020689755, 328141654053],
                [3, 2, 3, -2, -4], -1),
    "A154144": (13, [2, 8, 23, 53, 138, 312, 807, 1821, 4706, 10616, 27431, 61877, 159882, 360648, 931863, 2102013, 5431298, 12251432, 31655927, 71406581, 184504266, 416188056, 1075369671, 2425721757, 6267713762, 14138142488, 36530912903, 82403133173, 212917763658, 480280656552],
                [2, 6, 3, -6, -3], -1),
    "A154148": (21, [5, 7, 40, 50, 237, 295, 1384, 1722, 8069, 10039, 47032, 58514, 274125, 341047, 1597720, 1987770, 9312197, 11585575, 54275464, 67525682],
                [-5, -2, -3, 2, 6], 1),
    "A154150": (24, [1, 15, 24, 94, 145, 551, 848, 3214, 4945, 18735, 28824, 109198, 168001, 636455, 979184, 3709534, 5707105, 21620751, 33263448, 126014974],
                [-1, -14, -3, 14, 2], 1),
    "A154151": (25, [0, 18, 21, 111, 128, 650, 749, 3791, 4368, 22098, 25461, 128799, 148400, 750698, 864941, 4375391, 5041248, 25501650, 29382549, 148634511, 171254048, 866305418, 998141741, 5049197999, 5817596400, 29428882578, 33907436661, 171524097471, 197627023568],
                [0, -18, -3, 18, 1], 1),
    "A154153": (28, [6, 8, 47, 57, 278, 336, 1623, 1961, 9462, 11432, 55151, 66633, 321446, 388368, 1873527, 2263577, 10919718, 13193096, 63644783, 76895001, 370948982, 448176912, 2162049111, 2612166473, 12601345686, 15224821928, 73446025007, 88736765097, 428074804358, 517195768656],
                [-6, -2, -3, 2, 7], 1),
    "A154154": (30, [3, 13, 34, 84, 203, 493, 1186, 2876, 6915, 16765, 40306, 97716, 234923, 569533, 1369234, 3319484, 7980483, 19347373, 46513666],
                [-3, -10, -3, 10, 4], 1),
}
# g.f. = x * P(x) / (s * (x-1) * (x^2-2x-1) * (x^2+2x-1)), s = +1 or -1 by how the entry prints (1-x)
DEN = [-1, 1, 6, -6, -1, 1]  # (x-1)(x^4 - 6x^2 + 1) = -1 + x + 6x^2 - 6x^3 - x^4 + x^5
for name, (c, data, P, s) in ENTRIES.items():
    assert chains[c] == 2, name
    a = data[:4]
    while len(a) < 400:
        a.append(6 * a[-2] - a[-4] + 2)
    assert a[:len(data)] == data, name
    b = a[:5]
    while len(b) < 400:
        b.append(b[-1] + 6 * b[-2] - 6 * b[-3] - b[-4] + b[-5])
    assert b == a, name
    num = [0] + [s * p for p in P]  # numerator over DEN
    coef = []
    for n in range(401):
        v = num[n] if n < len(num) else 0
        v -= sum(DEN[j] * coef[n - j] for j in range(1, min(n, 5) + 1))
        coef.append(v // DEN[0])
    assert coef[0] == 0 and coef[1:] == a, name
    assert all(square_y(c, k) is not None for k in a), name
    print(f"{name} (c = {c}): m = 2, {len(data)} printed terms agree, the recurrence and the g.f. "
          f"agree with 400 terms of a(n) = 6a(n-2) - a(n-4) + 2, all of which are members")
