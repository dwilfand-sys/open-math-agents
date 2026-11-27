"""Render the independently replayed four-prime tree as explicit Lean case splits."""
from pathlib import Path
from functools import cache
from math import isqrt
from typing import NamedTuple

HERE = Path(__file__).parent

@cache
def next_prime(p):
    q = p + 2
    while any(q % t == 0 for t in range(3, isqrt(q) + 1, 2)):
        q += 2
    return q

class Node(NamedTuple):
    op: str
    left: object = None
    right: object = None

def read_tree(tokens):
    op = next(tokens)
    if op in ("A", "D"):
        return Node(op)
    first = read_tree(tokens)
    second = read_tree(tokens)
    return Node(op, second, first)

def bullet(lines):
    return ["· " + lines[0]] + ["  " + s for s in lines[1:]]

def ranges(chosen, start):
    row = list(chosen)
    while len(row) < 4:
        row.append((start, 2, False, False))
        start = next_prime(start)
    return row

def render(tree, chosen, start):
    if tree.op in ("A", "D"):
        coords = []
        for p, e, p_known, e_known in ranges(chosen, start):
            coords.append(f"⟨{p}, {e}, {str(p_known).lower()}, {str(e_known).lower()}⟩")
        return ["apply bad ![" + ", ".join(coords) + "]",
                "· unfold excluded; decide +kernel",
                "· intro i; fin_cases i <;> simp [covers] <;> omega"]
    if tree.op == "P":
        i = len(chosen)
        nxt = next_prime(start)
        left = render(tree.left, chosen + ((start, 2, True, False),), nxt)
        right = []
        low = start
        for j in range(i,4):
            high = next_prime(low)
            right.append(f"have p{j}ge{high} : {high} ≤ p {j} := "
                         f"skip_composites (a := {low}) (hp {j}) (by omega) (by decide)")
            low = high
        right.extend(render(tree.right, chosen, nxt))
        return [f"by_cases h : p {i} = {start}"] + bullet(left) + bullet(right)
    i = int(tree.op)
    p,e,_,_ = chosen[i]
    lf = chosen[:i] + ((p,e,True,True),) + chosen[i+1:]
    rg = chosen[:i] + ((p,e+2,True,False),) + chosen[i+1:]
    return [f"by_cases h : e {i} = {e}"] + bullet(render(tree.left,lf,start)) + bullet(render(tree.right,rg,start))

def build():
    path = HERE / "FourPrimeExclusion.lean"
    current = path.read_text(encoding="utf8")
    start = current.index("  by_cases h : p 0 = 3")
    end = current.index("/-- No odd almost-perfect square")
    tokens = iter((HERE / "boxes_4.txt").read_text(encoding="ascii").strip())
    tree = read_tree(tokens)
    assert next(tokens, None) is None
    source = "".join("  " + line + "\n" for line in render(tree, (), 3))
    path.write_bytes((current[:start] + source + "\n" + current[end:]).encode("utf8"))

if __name__ == "__main__":
    build()
