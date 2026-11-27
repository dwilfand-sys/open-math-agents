"""Replay the independent prime sieve for every new positive-slope signature."""
import json
from pathlib import Path
from sys import argv

from lagneau_extra_one_replay import replay


table = json.loads(Path(argv[1]).read_text())
replay({
    "slopes": table["slopes"],
    "smallThresholds": [1],
    "maxDivisor": table["nextLower"],
    "upper": table["upper"],
    "blockSize": table["nextBlock"],
    "counts": [table["extraCounts"]],
    "factors": [table["extraFactors"]],
})
