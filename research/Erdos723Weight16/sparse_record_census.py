"""Summarize the archived seed orbits and optionally compare every raw native tuple."""
import argparse
from collections import Counter
from pathlib import Path

from other_sparse_cases import seed_orbits
from sparse_records import read_records
from weight16_exact_cover import StartingCase, WORDS


def census(case,records,native=None):
    labels=tuple(tuple(j) for j,_ in records['0']['seed'])
    seeds,raw=seed_orbits(case,labels)
    if set(records)!=set(map(str,range(len(seeds)))):
        raise ValueError('invalid orbit coverage')
    total=restored=blocked=at_least_51=0
    hidden=Counter()
    for i,(seed,weight) in enumerate(seeds):
        row=records[str(i)]
        if row['orbit_size']!=weight or tuple((tuple(j),tuple(m)) for j,m in row['seed'])!=seed:
            raise ValueError('incorrect seed weighting')
        interiors=row['inside']
        if native is not None:
            p=native/f'cube-seed-{i:02d}.txt'
            native_rows=[tuple(map(int,s.split(','))) for s in p.read_text().splitlines()]
            given=[tuple(b for _,b in x['blocks']) for x in interiors]
            if len(given)!=len(set(given)) or sorted(given)!=sorted(native_rows):
                raise ValueError(f'native traversal differs at seed {i}')
        total+=len(interiors)
        restored+=weight*len(interiors)
        for x in interiors:
            n=x['hidden_options']
            hidden[n]+=1
            at_least_51+=n>=51
            blocked+=x['missing_pair'] is not None
    print(f'{case.word:#x}: {raw} starts, {len(seeds)} orbits, {total} interiors, {restored} labelled; '
          f'{blocked} blocked, {at_least_51} with at least 51 hidden options, range {min(hidden)}-{max(hidden)}.')
    if native:
        print('All native raw assignment lists agree exactly.')


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('case',type=int,choices=range(6))
    ap.add_argument('records',type=Path)
    ap.add_argument('--native-dir',type=Path)
    args=ap.parse_args()
    census(StartingCase(WORDS[args.case]),read_records(args.records),args.native_dir)
