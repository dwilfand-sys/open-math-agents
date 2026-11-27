"""Exhaust the low and high bits of small examples of the star correction."""
from fractions import Fraction as F
from itertools import product
from random import Random


def configurations(weights):
    for bits in product((0, 1), repeat=len(weights)):
        prob = F(1)
        for x, b in zip(weights, bits):
            prob *= x if b else 1-x
        yield bits, prob


def test():
    rng = Random(300984)
    for _ in range(100):
        low = [F(rng.randrange(1,6),7) for _ in range(4)]
        high = [F(rng.randrange(1,6),7) for _ in range(3)]
        # The old event can be arbitrary in the low coordinates.
        old = {bits for bits, _ in configurations(low) if rng.randrange(3)}
        neighbors = [{j for j in range(len(high)) if rng.randrange(2)} for i in low]
        prior = sum(w for bits,w in configurations(low) if bits in old)
        exact = sum(w*v for bits,w in configurations(low) if bits in old
                    for flags,v in configurations(high)
                    if not any(bits[i] and flags[j] for i,N in enumerate(neighbors) for j in N))
        events = []
        for i,N in enumerate(neighbors):
            survival=F(1)
            for j in N:
                survival *= 1-high[j]
            events.append((1-survival,i))
        events.sort(reverse=True)
        none, loss=F(1),F(0)
        for j,(hit,i) in enumerate(events):
            none *= 1-low[i]
            next_hit = events[j+1][0] if j+1<len(events) else 0
            loss += (hit-next_hit)*max(0,prior-none)
        assert exact <= prior-loss <= prior
    print("100 exact product-space examples passed.")


if __name__=='__main__':
    test()
