"""Replay every negative-slope prime-pair count and rounded block product."""

from argparse import ArgumentParser
import json
from math import gcd, isqrt
from pathlib import Path

from lagneau_large_singletons_check import odd_segment, sieve_primes


def replay_row(s, lower, upper, block, primes):
    first = (lower-5)//6+1
    stop = (upper-5)//6+1
    a, b = 12*s, 10*s-1
    # Write a composite shifted value as l*t. Solve for t modulo a, in
    # contrast with solving for the progression index modulo l.
    progressions = [(l, b*pow(l, -1, a) % a) for l in primes
                    if l*l <= 2*s*upper-1 and gcd(l, a) == 1]
    total, factor, blocks = 0, 10**15, 0
    for start in range(first, stop, 8*block):
        length = min(8*block, stop-start)
        base = odd_segment(6*start+5, 3*length-2, primes)[::3]
        shifted = bytearray([1])*length
        lo, hi = a*start+b, a*(start+length-1)+b
        for l, residue in progressions:
            if l*l > hi:
                break
            t = max(l, -(-lo//l))
            t += (residue-t) % a
            pos = (l*t-lo)//a
            if pos < length:
                shifted[pos::l] = bytes((length-1-pos)//l+1)
        for i in range(0, length, block):
            end = min(i+block, length)
            flags = int.from_bytes(base[i:end], 'little') & int.from_bytes(shifted[i:end], 'little')
            count = flags.bit_count()
            top = 6*(start+end-1)+5
            total += count
            factor = (factor*top+top+count-1)//(top+count)
            blocks += 1
    return total, factor, blocks


def main():
    parser = ArgumentParser()
    parser.add_argument('table', type=Path)
    args = parser.parse_args()
    data = json.loads(args.table.read_text(encoding='utf-8'))
    upper, block = data['upper'], data['blockSize']
    primes = sieve_primes(isqrt(2*max(row['s'] for row in data['slopes'])*upper))
    for row in data['slopes']:
        s, lower = row['s'], row['lower']
        assert lower == data['maxDivisor']//s
        actual = replay_row(s, lower, upper, block, primes)
        expected = row['count'], int(row['factor']), row['blocks']
        if actual != expected:
            raise ValueError(f'slope {s}: computed {actual}, expected {expected}')
        print(f'slope {s}: {actual[0]} pairs, multiplier {actual[1]} at scale 10^15', flush=True)


if __name__ == '__main__':
    main()
