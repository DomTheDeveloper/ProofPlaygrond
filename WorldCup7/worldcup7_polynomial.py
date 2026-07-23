"""Exact seven-team counting polynomial in binomial and centered forms."""
from math import comb

H_HALF = [
    1,
    1824,
    1199145,
    232852850,
    17547150075,
    620856948600,
    11670877850282,
    126571440305244,
    837957254969529,
    3521931467666680,
    9653611080929469,
    17561784201419010,
    21415558464270922,
]
H_STAR = H_HALF + H_HALF[-2::-1]

COUNTS_0_TO_12 = [
    1,
    1854,
    1254330,
    269680320,
    25099425960,
    1261570701636,
    39660539404661,
    862295098189344,
    13926292882237119,
    176080027218850650,
    1813557723086696790,
    15691346140563786336,
    116857054129381000771,
]

# Q(y), coefficients from y^0 through y^12.
Q_COEFF_LOW_TO_HIGH = [
    3154971657218398617600000,
    1338033873961407109939200,
    271550071954942194604032,
    46788350432653174464576,
    6155573446929541440848,
    844891531636894661036,
    95377188765692157983,
    8739034660779266186,
    1570392939902887193,
    45058773949238216,
    37765555858458113,
    -3685861337229214,
    606027774191831,
]
DENOMINATOR = 63155442812426442532454400000  # 29!/140


def F7_binomial(r: int) -> int:
    """Evaluate F_7(r) for any nonnegative integer r."""
    if r < 0:
        raise ValueError("r must be nonnegative")
    return sum(h * (comb(r + 29 - j, 29) if r + 29 - j >= 29 else 0)
               for j, h in enumerate(H_STAR))


def F7_centered(r: int) -> int:
    """Evaluate the centered factored formula, with an exact divisibility check."""
    if r < 0:
        raise ValueError("r must be nonnegative")
    x = r + 3
    y = x * x
    q = 0
    for coefficient in reversed(Q_COEFF_LOW_TO_HIGH):
        q = q * y + coefficient
    numerator = x * (x*x - 1) * (x*x - 4) * q
    quotient, remainder = divmod(numerator, DENOMINATOR)
    if remainder:
        raise ArithmeticError("formula did not evaluate integrally")
    return quotient


if __name__ == "__main__":
    for r, expected in enumerate(COUNTS_0_TO_12):
        a = F7_binomial(r)
        b = F7_centered(r)
        assert a == b == expected, (r, a, b, expected)
    assert H_STAR == H_STAR[::-1]
    assert F7_binomial(13) == 763843960352898954144
    assert F7_binomial(14) == 4452841840686426708039
    print("All exact checks passed.")
    print("F7(13) =", F7_binomial(13))
    print("F7(14) =", F7_binomial(14))
