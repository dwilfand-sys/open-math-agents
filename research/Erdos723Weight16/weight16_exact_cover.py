"""Exact-cover encoding of the sparse weight-16 starting cases of Carter.

The two families of lines are A (eight four-secants) and B (72 two-secants).
A weight-16 point is an edge of the complement of the cubic graph on A.
The exact-cover columns assert the pair intersections outside the weight-16
set. All 95 outside points, including the 51 on no A-line, are recovered
from a solution. Run without arguments for counts, or --matrix CASE PATH
for a SciPy sparse matrix with one column per constraint, one row per
possible outside point. Case indices use the canonical upstream word list.
"""
import argparse
from collections import Counter
from itertools import combinations
from pathlib import Path

WORDS = (0x1da9807, 0x2e69807, 0x3569807, 0x35a5807, 0x3da1087, 0xfc02187)
A_PAIRS = tuple(combinations(range(8), 2))

class StartingCase:
    def __init__(self, word):
        self.word = word
        self.double_types = [pair for k, pair in enumerate(A_PAIRS) if word & (1 << k)]
        self.support = [pair for pair in A_PAIRS if pair not in self.double_types]
        assert len(self.double_types) == 12 and len(self.support) == 16
        assert all(sum(a in pair for pair in self.double_types) == 3 for a in range(8))
        self.support_sets = [set(pair) for pair in self.support]
        self.lines = [(s,t) for s,t in combinations(range(16),2)
                      if self.support_sets[s].isdisjoint(self.support_sets[t])]
        assert len(self.lines) == 72
        self.line_index = {pair: i for i, pair in enumerate(self.lines)}
        missing = [(edge,a) for edge,(s,t) in enumerate(self.lines) for a in range(8)
                   if a not in self.support[s] and a not in self.support[t]]
        nonintersecting = [(i,j) for i,j in combinations(range(72),2)
                           if set(self.lines[i]).isdisjoint(self.lines[j])]
        assert len(missing) == 288 and len(nonintersecting) == 1980
        self.dd_col = {p:i for i,p in enumerate(self.double_types)}
        self.ba_col = {p:i+12 for i,p in enumerate(missing)}
        self.bb_col = {p:i+300 for i,p in enumerate(nonintersecting)}
        self.num_constraints = 2280
        self.adjacency = [0] * 16
        for s,t in self.lines:
            self.adjacency[s] |= 1 << t
            self.adjacency[t] |= 1 << s
        assert all(m.bit_count() == 9 for m in self.adjacency)

    def matchings(self, remaining, prefix=()):
        if not remaining:
            yield tuple(sorted(prefix))
            return
        first_bit = remaining & -remaining
        s = first_bit.bit_length()-1
        rest = remaining ^ first_bit
        neighbors = self.adjacency[s] & rest
        while neighbors:
            bit = neighbors & -neighbors
            t = bit.bit_length()-1
            yield from self.matchings(rest ^ bit, prefix+(self.line_index[s,t],))
            neighbors ^= bit

    def candidates(self):
        for rows in [()] + [(r,) for r in range(8)] + self.double_types:
            available = sum(1 << i for i, pair in enumerate(self.support_sets)
                            if pair.isdisjoint(rows))
            assert available.bit_count() == 16 - 4 * len(rows)
            for matching in self.matchings(available):
                yield rows, matching

    def constraint_indices(self, rows, matching):
        answer = [self.dd_col[rows]] if len(rows) == 2 else []
        answer.extend(self.ba_col[e,a] for e in matching for a in rows)
        answer.extend(self.bb_col[p] for p in combinations(matching,2))
        return answer

    def count(self):
        groups = Counter()
        coverage = [0]*self.num_constraints
        for rows, matching in self.candidates():
            constraints = self.constraint_indices(rows, matching)
            assert len(constraints) == (28, 21, 15)[len(rows)]
            assert len(constraints) == len(set(constraints))
            groups[len(rows)] += 1
            for i in constraints:
                coverage[i] += 1
        assert min(coverage) > 0
        return [groups[i] for i in range(3)], (min(coverage),max(coverage))

    def output_matrix(self, filename):
        from scipy import sparse
        from array import array
        values = array('i')
        offset = [0]
        for rows, matching in self.candidates():
            values.extend(self.constraint_indices(rows, matching))
            offset.append(len(values))
        matrix = sparse.csr_matrix(([1]*len(values),values,offset),
                                   shape=(len(offset)-1,self.num_constraints),dtype='int8')
        sparse.save_npz(filename,matrix)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--matrix',nargs=2,metavar=('CASE','PATH'))
    args = parser.parse_args()
    if args.matrix:
        case,path=args.matrix
        index=int(case)
        if index not in range(6):
            parser.error('CASE must lie between 0 and 5')
        StartingCase(WORDS[index]).output_matrix(Path(path))
    else:
        for i,word in enumerate(WORDS):
            counts,bounds=StartingCase(word).count()
            print(f'{i}: {word:#09x}: empty/single/double = {counts}, total {sum(counts)}, column frequencies {bounds}')

