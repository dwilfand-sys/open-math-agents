"""Combine the separately certified pair and triple Janson tables for A300984.

Usage: python lagneau_certificate_union.py Wide1B.json Triple1B.json Combined.json
The output can be passed to lagneau_billion_graph_bound.cjs instead of Wide1B.json.
"""

import argparse
import json
from fractions import Fraction
from math import factorial
from pathlib import Path


def read_bound(row, precision, triples):
    scale = 10**15
    mean = Fraction(int(row["lowerEdgeFirst" if triples else "lowerFirst"]), precision**2)
    if triples:
        mean += Fraction(int(row["lowerTripleFirst"]), precision**3)
        overlap = Fraction(int(row["upperVertexStars"]), precision**5)
        overlap += Fraction(int(row["upperPairStars"]), precision**4)
    else:
        overlap = Fraction(int(row["upperOrderedStars"]), precision**3)
    exponent = max(Fraction(), mean - overlap / 2)
    bound = scale / sum(exponent**j / factorial(j) for j in range(7))
    upper = -(-bound.numerator // bound.denominator)
    assert upper == int(row["survivalUpper"])
    return upper


def combine(pairs, triples):
    for name in ("cap", "B", "precision"):
        assert pairs[name] == triples[name]
    assert pairs["cap"] == 10**9 and pairs["B"] == 73
    scale = pairs["precision"]
    values = [{r["small"]: r for r in table["rows"]} for table in (pairs, triples)]
    assert values[0].keys() == values[1].keys() and len(values[0]) == 16
    rows = []
    for mask in sorted(values[0]):
        p, t = (v[mask] for v in values)
        assert p["vertices"] == t["vertices"] and p["edges"] == t["edges"]
        assert p["lowerFirst"] == t["lowerEdgeFirst"]
        upper = min(read_bound(p, scale, False), read_bound(t, scale, True))
        rows.append({"small": mask, "survivalUpper": str(upper)})
    return {k: pairs[k] for k in ("cap", "B", "precision")} | {"rows": rows}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("pairs", "triples", "output"):
        parser.add_argument(key, type=Path)
    args = parser.parse_args()
    table = combine(json.loads(args.pairs.read_text()), json.loads(args.triples.read_text()))
    args.output.write_text(json.dumps(table, indent=2) + "\n", encoding="utf-8")
