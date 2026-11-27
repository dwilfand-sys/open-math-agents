"""Exact finite product-space tests for the gated, mixed and mandatory stars."""

from fractions import Fraction as Q
from itertools import product
from math import prod


def none(indices, weights):
    return prod((1-weights[i] for i in set(indices)), start=Q(1))


def state_weights(weights):
    den = prod(p.denominator for p in weights)
    for bits in product((0, 1), repeat=len(weights)):
        num = prod(p.numerator if bit else p.denominator-p.numerator
                   for p, bit in zip(weights, bits))
        yield bits, num, den


def risk_function(rows, gate, weights):
    """Compute Q(h) both by the product formula and enumeration of the low coordinates."""
    forced_leaves = next((leaves for t, _, leaves in rows if t is None), set())
    risks = []
    for t, layer, leaves in rows:
        if layer:
            assert leaves.isdisjoint(forced_leaves)
            leaves = leaves | forced_leaves
        risks.append((t, layer, 1-none(leaves, weights)))
    bounds = []
    exact_none = {}
    for h in sorted({risk for _, _, risk in risks}):
        eligible = [(t, layer) for t, layer, risk in risks if risk >= h]
        old = {t for t, layer in eligible if t is not None and not layer}
        large = {t for t, layer in eligible if layer}
        forced = any(t is None for t, _ in eligible)
        assert not large.intersection(old | gate)
        expected = 0 if forced else none(old, weights)-none(old|gate, weights)*(1-none(large, weights))
        measured = Q(0)
        for bits, n, d in state_weights(weights[:6]):
            available = any(t is None or (bits[t] and (not layer or not any(bits[s] for s in gate)))
                            for t, layer in eligible)
            if not available:
                measured += Q(n, d)
        assert measured == expected
        # Check the directions used when only probability intervals are known.
        low = [w*Q(9, 10) for w in weights]
        high = [min(1, w*Q(11, 10)) for w in weights]
        upward = 0 if forced else none(old, low)-none(old|gate, high)*(1-none(large, low))
        assert expected <= upward
        bounds.append((h, upward))
        exact_none[h] = expected

    def transform(u, exact=False):
        loss = Q(0)
        prev = Q(0)
        for h, upper in bounds:
            no_trigger = exact_none[h] if exact else upper
            loss += (h-prev)*max(0, u-no_trigger)
            prev = h
        return u-loss

    return transform


def survives_rows(bits, rows, gate):
    gate_open = not any(bits[t] for t in gate)
    return not any((t is None or bits[t]) and (not layer or gate_open)
                   and any(bits[r] for r in leaves) for t, layer, leaves in rows)


def check(mandatory):
    # Coordinates 0..5 are low centers, 6..8 and 9..11 the two leaf signs.
    weights = [Q(1, 3), Q(2, 7), Q(2, 5), Q(3, 8), Q(1, 4), Q(2, 9),
               Q(2, 5), Q(1, 3), Q(1, 4), Q(3, 7), Q(2, 5), Q(1, 3)]
    gates = ({0}, {1})
    # Old neighbor sets overlap each other and the gated sets. Centers 2,3
    # occur on both signs, modelling a mixed row with fixed small multiplier.
    rows = (
        [(0, False, {7}), (2, False, {7, 8}), (3, False, {8}), (4, True, {6, 7})],
        [(1, False, {10}), (2, False, {11}), (3, False, {10, 11}), (5, True, {9, 10})],
    )
    if mandatory:
        rows[0].append((None, False, {8}))
    transforms = [risk_function(row, gate, weights) for row, gate in zip(rows, gates)]
    cases = [dict(old=0, neg=0, pos=0, both=0) for _ in range(16)]
    for bits, n, den in state_weights(weights):
        ok = [survives_rows(bits, row, gate) for row, gate in zip(rows, gates)]
        for choice, case in enumerate(cases):
            # When the corresponding gate is closed, the old test really
            # may use the low part of that high-leaf interval.
            if ((choice & 1 and bits[0] and bits[6])
                    or (choice & 2 and bits[1] and bits[9])
                    or (choice & 4 and bits[3] and bits[4])
                    or (choice & 8 and bits[0] and bits[5])):
                continue
            case['old'] += n
            case['neg'] += n*ok[0]
            case['pos'] += n*ok[1]
            case['both'] += n*(ok[0] and ok[1])
    for case in cases:
        old, neg, pos, both = (Q(case[k], den) for k in ('old', 'neg', 'pos', 'both'))
        for exact in (True, False):
            minus, plus = transforms
            assert neg <= minus(old, exact) and pos <= plus(old, exact)
            for upper in (old, (1+old)/2, Q(1)):
                assert both <= plus(minus(upper, exact), exact)
                assert both <= minus(plus(upper, exact), exact)
    return len(cases)


if __name__ == '__main__':
    print('Verified', sum(check(mandatory) for mandatory in (False, True)),
          'exact 12-coordinate examples in both sign orders.')
