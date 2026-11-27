from itertools import permutations
from collections import Counter
from weight16_exact_cover import StartingCase,WORDS
def permutation_images(case):
    ds = set(case.double_types)
    for p in permutations(range(8)):
        if all(tuple(sorted((p[i],p[j]))) in ds for i,j in ds):
            yield p
def line_image(case,p):
    sv={edge:i for i,edge in enumerate(case.support)}
    S=[sv[tuple(sorted((p[a],p[b])))] for a,b in case.support]
    return [case.line_index[tuple(sorted((S[a],S[b])))] for a,b in case.lines]
if __name__=='__main__':
    c=StartingCase(WORDS[4])
    perms=[line_image(c,p) for p in permutation_images(c)]
    orbits=sorted({tuple(sorted({p[e] for p in perms})) for e in range(72)})
    empty=Counter(e for J,m in c.candidates() if not J for e in m)
    for orb in orbits:
        assert all(empty[e]==empty[orb[0]] for e in orb)
        print(orb[0],len(orb),empty[orb[0]])

