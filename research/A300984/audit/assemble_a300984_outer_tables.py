"""Pack the independently replayed 30,000-to-50,000 center batches."""

from gzip import compress
from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EXPECTED = {
    "Positive": (23136, "991fefbc76a1f2fdcbf2d888617a3b16b09901710347a90b2151941e06397454"),
    "Negative": (10362, "76536306b77fb15ee0a52646cec3b178e45d13528fb27979e75aa4103474636d"),
}

for sign, (rows, digest) in EXPECTED.items():
    data = "".join((ROOT / f"CunninghamOuter{sign}{end}.txt").read_text()
                   for end in range(31000, 51000, 1000)).encode("ascii")
    assert len(data.splitlines()) == rows and sha256(data).hexdigest() == digest
    output = ROOT / f"CunninghamOuter{sign}30000To50000.txt.gz"
    output.write_bytes(compress(data, compresslevel=9, mtime=0))
    print(output.name, rows, digest)
