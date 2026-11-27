"""Remove Lifchitz's last three decade totals from the singleton bound."""

from fractions import Fraction
from math import factorial
from pathlib import Path
import sys

from check_a300984_published_singletons import COUNTS, reciprocal_lower


def no_high_proportion(numerator, paths):
    windows = [tuple(map(int, row.split())) for p in paths for row in p.read_text().splitlines()]
    windows.sort()
    assert all(a < b and n >= 0 for a,b,n in windows)
    assert all(b <= c for (_,b,_),(c,_,_) in zip(windows,windows[1:]))
    mass = Fraction()
    for exponent,low_count,high_count in zip((10,11),COUNTS,COUNTS[1:]):
        lo,hi=10**exponent,10**(exponent+1)
        cells=[(a,b,n) for a,b,n in windows if lo<=a<b<=hi]
        remaining=high_count-low_count-sum(n for a,b,n in cells)
        assert remaining>=0
        mass+=sum(reciprocal_lower(b,n) for a,b,n in cells)+reciprocal_lower(hi,remaining)
    mass+=sum(reciprocal_lower(b,n) for a,b,n in windows if a>=10**12)
    ratio=Fraction(numerator,10**15)/sum(mass**k/factorial(k) for k in range(6))
    return (ratio*10**12).__ceil__()


if __name__=="__main__":
    print(no_high_proportion(int(sys.argv[1]),list(map(Path,sys.argv[2:]))),"/ 10^12")
