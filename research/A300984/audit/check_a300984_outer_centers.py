"""Generate and independently verify small, resumable batches of center rows."""

from argparse import ArgumentParser
from pathlib import Path
from subprocess import run


def batches(directory, sign, last):
    for lower in range(10000, last, 1000):
        name = f"CunninghamOuter{sign.title()}{lower + 1000}.txt"
        target = directory / name
        if target.exists():
            continue
        provisional = target.with_suffix(".pending")
        with provisional.open("w") as output:
            run([str(directory / "CunninghamOuterStars.exe"), str(lower + 1000),
                 sign, str(lower), "14000000", "100000000"], stdout=output, check=True)
        checked = run(["node", str(directory / "check_a300984_conditional_stars.cjs"),
                       str(provisional), sign, "14000000", "100000000"],
                      capture_output=True, text=True, check=True)
        rows = [line.split() for line in provisional.read_text().splitlines()]
        centers = {int(row[0]) for row in rows}
        replayed = {int(line.split()[0]) for line in checked.stdout.splitlines()}
        assert centers == replayed and all(lower < t <= lower + 1000 for t in centers)
        assert len(rows) == len(centers) * (32 if sign == "positive" else 11)
        provisional.replace(target)
        print(sign, lower+1000, len(rows), flush=True)


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("sign", choices=["positive", "negative"])
    parser.add_argument("last", type=int)
    args = parser.parse_args()
    if not 11000 <= args.last <= 100000 or args.last % 1000:
        raise SystemExit("Invalid endpoint")
    batches(Path(__file__).resolve().parent, args.sign, args.last)
