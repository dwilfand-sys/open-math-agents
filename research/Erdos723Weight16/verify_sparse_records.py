"""Check every reported missing meeting directly in the 80-row incidence model."""
import argparse
from functools import cache
from pathlib import Path

from inside_blocks import bits
from scales_block_consistency import members
from scales_fixed_intersection import block_supports
from verify_case4_relaxations import checked_cover_columns
from weight16_exact_cover import StartingCase, WORDS
from sparse_records import read_records


def verify(case, records):
    blocks = block_supports(case)
    total = tested = 0
    @cache
    def meetings(b,c):
        endpoint = set(case.lines[b]) | set(case.lines[c])
        if len(endpoint)!=4:
            raise ValueError('pair has a meeting on the support')
        remaining = bits(set(range(16))-endpoint)
        return [bits((b,c,*matching)) for matching in case.matchings(remaining)]

    for row in records.values():
        fixed = {(tuple(j),bits(m)) for j,m in row['seed']}
        for terminal in row['inside']:
            points = set()
            for a,i in terminal['blocks']:
                doubles,singles = blocks[a][i]
                points.update(doubles)
                points.update(((a,),m) for m in singles)
            if len(points)!=44 or not fixed<=points:
                raise ValueError('incorrect nonhidden exterior point set')
            used = set()
            for j,m in points:
                hits=checked_cover_columns(case,j,list(members(m)))
                if not used.isdisjoint(hits):
                    raise ValueError('duplicate incidence in explicit record')
                used.update(hits)
            if not set(range(300))<=used:
                raise ValueError('record misses an A/A or A/B meeting')
            b,c=terminal['missing_pair']
            if case.bb_col[b,c] in used:
                raise ValueError('chosen pair already meets at a nonhidden point')
            masks=[m for _,m in points]
            candidates=meetings(b,c)
            if any(all((candidate&m).bit_count()<=1 for m in masks) for candidate in candidates):
                raise ValueError('chosen pair admits a hidden meeting')
            total+=1
            tested+=len(candidates)
    print(f'word {case.word:#x}: {total} literal interiors and {tested} possible missing-pair meetings checked.')


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('case',type=int,choices=range(6))
    ap.add_argument('input',type=Path)
    args=ap.parse_args()
    verify(StartingCase(WORDS[args.case]), read_records(args.input))
