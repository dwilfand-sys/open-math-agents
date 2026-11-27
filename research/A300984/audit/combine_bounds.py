"""Combine the one-outer-prime numerator and three-witness denominator bounds."""

from fractions import Fraction as Q


lower_invsqrt = Q(707106781186547,10**15)
upper_invsqrt = lower_invsqrt + Q(1,10**15)
assert 2*lower_invsqrt**2 < 1 < 2*upper_invsqrt**2
squarefree_lower = Q(849112766182137,10**15)
second_pair_loss = Q(6980795097,10**12)
third_triple_loss = Q(207592750,10**12)
tail = Q(1,19999)
loss = ((1-lower_invsqrt)*(1-squarefree_lower)
        +(upper_invsqrt-Q(1,2))*(second_pair_loss+2*tail)
        +Q(1,2)*(third_triple_loss+3*tail))
numerator_upper = Q(527775952949857,10**15)
ratio_upper = numerator_upper/(1-loss)
assert ratio_upper == Q(10554991283044190143000000000000000,
                        19082263250482905356804459392486939)
assert ratio_upper < Q(553131,1000000)
print("Exact upper bound",ratio_upper)
print("Limiting upper proportion < 55.3131%")
