"""Check literal inside-point records, their group orbit, and the final missing partners."""
import json
from itertools import combinations
from pathlib import Path

from scales_fixed_intersection import case_data, act
from scales_forced_doubles import two_cases
from verify_case4_relaxations import checked_cover_columns


if __name__ == '__main__':
    c, group = case_data()
    records = json.loads(Path(__file__).with_name('Case4InsideConfigurations.json').read_text(encoding='utf8'))
    starts = list(two_cases(c, group))
    all_orbits = set()
    empty_matchings = [set(m) for m in c.matchings((1 << 16)-1) if 35 in m]
    for k in range(2):
        fixed = starts[k]
        scope = [g for g in group if tuple(sorted(act(v, *g) for v in fixed)) == fixed]
        assert len(scope) == 4
        for saved in records[str(k)]['inside']:
            points = tuple(sorted((tuple(j),tuple(m)) for j,m in saved['points']))
            assert len(points) == len(set(points)) == 44 and set(fixed) <= set(points)
            used = set()
            for j, m in points:
                assert j
                columns = checked_cover_columns(c, j, m)
                assert used.isdisjoint(columns)
                used.update(columns)
            assert set(range(300)) <= used
            all_orbits.add(min(tuple(sorted(act(p,*g) for p in points)) for g in scope))
            inside = [set(m) for _,m in points]
            hidden = [m for m in empty_matchings if all(len(t & m) <= 1 for t in inside)]
            missing = [b for b in range(72) if b != 35 and set(c.lines[b]).isdisjoint(c.lines[35])
                       and not any({b,35} <= t for t in inside + hidden)]
            assert len(hidden) == saved['permitted_hidden_matchings'] == 8
            assert missing == saved['uncovered_B_partners'] and len(missing) == 12
            print('missing B35 partners:', missing)
    assert len(records['0']['inside']) == 4 and len(records['1']['inside']) == 0
    assert len(all_orbits) == 1
    print('All four literal 44-point records verified; one orbit under the stabilizer.')
