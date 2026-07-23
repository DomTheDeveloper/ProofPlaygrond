"""Independent regression check against Zeilberger's published six-team polynomial."""
import sympy as sp
from math import comb

r = sp.symbols("r")
counts = [1, 265, 27990, 1244390, 29714285, 451632015, 4883772645, 40512697755]
h_half = [sum((-1)**i * comb(20, i) * counts[k-i] for i in range(k+1))
          for k in range(8)]
h = h_half + h_half[::-1]
ours = sp.expand_func(sum(sp.Integer(h[j]) * sp.binomial(r + 19 - j, 19)
                          for j in range(16)))

published = sp.Rational(1, 10137091700736000) * (2*r+5)*(r+4)*(r+3)*(r+2)*(r+1) * (
    55156451*r**14 + 1930475785*r**13 + 31426751500*r**12 +
    315397914875*r**11 + 2181374421522*r**10 + 11011717259925*r**9 +
    41921602480600*r**8 + 122633173357625*r**7 + 278241144318203*r**6 +
    490506924963670*r**5 + 667964358905100*r**4 + 691864584471000*r**3 +
    528464246017824*r**2 + 278397371589120*r + 84475764172800)

assert sp.expand(ours - published) == 0
print("The recurrence/reconstruction exactly reproduces the published n=6 polynomial.")
