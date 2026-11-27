"""Verify the extension using the independent factor-progression sieve."""
import json
from math import isqrt
from pathlib import Path
from sys import argv

from lagneau_large_singletons_check import sieve_primes
from lagneau_negative_replay import replay_row


rows = [json.loads(line) for line in Path(argv[1]).read_text().splitlines()]
primes = sieve_primes(isqrt(2 * max(row['slope']*row['upper'] for row in rows)))
for row in rows:
    observed = replay_row(row['slope'], row['lower'], row['upper'], row['block'], primes)
    expected = row['count'], int(row['factor']), row['blocks']
    if observed != expected:
        raise ValueError((row['slope'], observed, expected))
    print(row['slope'], *observed, flush=True)
