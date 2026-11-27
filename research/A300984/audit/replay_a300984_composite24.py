"""Rebuild or replay the complete A300984 24-pair certificate input files."""

from argparse import ArgumentParser
from gzip import decompress
from hashlib import sha256
from json import loads
from pathlib import Path
from subprocess import run


def replay(generator=None):
    root=Path(__file__).resolve().parent
    manifest=loads((root/"A300984Composite24InputHashes.json").read_text())
    for item in manifest:
        path=root/item["file"]
        zipped=path.with_suffix(".txt.gz")
        if generator is not None:
            with path.open("w") as output:
                run([str(generator.resolve()),str(item["sign"]),str(item["lower"]),
                     str(item["upper"])],stdout=output,check=True)
        source=path if path.exists() else zipped
        raw=decompress(source.read_bytes()) if source.suffix==".gz" else source.read_bytes()
        data=raw.replace(b"\r\n",b"\n")
        assert len(data.splitlines())-1==item["rows"] and sha256(data).hexdigest()==item["sha256"]
        run(["node",str(root/"check_a300984_composite_slopes.cjs"),str(source)],check=True)


if __name__=="__main__":
    parser=ArgumentParser()
    parser.add_argument("--generator",type=Path)
    replay(parser.parse_args().generator)
