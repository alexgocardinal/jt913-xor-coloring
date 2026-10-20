#!/usr/bin/env python3
"""Generate generalized Kneser graphs and the Jensen--Toft 9.13 XOR family.

The graph K(n,k,t) has the k-subsets of [0,n) as vertices, with S--U an
edge exactly when |S intersect U| < t. For n=2k a power of two and t=k-1,
``xor_center`` gives an optimal coloring, proved separately in the paper.

No third-party modules are required. The explicit graph writer is intended
for small graphs; the coloring functions work with individual vertices at
arbitrarily large powers of two without constructing the whole graph.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from itertools import combinations
import json
import math
from pathlib import Path


def vertices(n: int, k: int) -> list[tuple[int, ...]]:
    if not (0 <= k <= n):
        raise ValueError("Require 0 <= k <= n")
    return list(combinations(range(n), k))


def is_edge(s: tuple[int, ...], u: tuple[int, ...], t: int) -> bool:
    """Adjacency in K(n,k,t), assuming distinct k-subsets s and u."""
    return len(set(s).intersection(u)) < t


def graph(n: int, k: int, t: int) -> tuple[list[tuple[int, ...]], list[list[int]]]:
    if not (0 <= t <= k):
        raise ValueError("Require 0 <= t <= k")
    vs = vertices(n, k)
    adj: list[list[int]] = [[] for _ in vs]
    masks = [sum(1 << x for x in v) for v in vs]
    for j in range(1, len(vs)):
        for i in range(j):
            if bin(masks[i] & masks[j]).count("1") < t:
                adj[i].append(j)
                adj[j].append(i)
    return vs, adj


def xor_center(s: tuple[int, ...], n: int) -> tuple[int, ...]:
    """Center of S's star/top fiber when n=2k is a power of two."""
    if n < 2 or n & (n - 1) or len(s) * 2 != n:
        raise ValueError("Require a middle-layer set and n >= 2 a power of two")
    if len(set(s)) != len(s) or any(x < 0 or x >= n for x in s):
        raise ValueError("S must be a subset of [0,n)")
    x = 0
    for label in s:
        x ^= label
    return tuple(sorted(set(s) ^ {x}))


def fiber(center: tuple[int, ...], n: int) -> list[tuple[int, ...]]:
    """All middle-layer sets in a zero-XOR star or top."""
    k = n // 2
    if n < 2 or n & (n - 1) or len(set(center)) != len(center):
        raise ValueError("Invalid center or ground set")
    if any(x < 0 or x >= n for x in center) or len(center) not in (k - 1, k + 1):
        raise ValueError("Center must be a (k-1)- or (k+1)-set")
    x = 0
    for label in center:
        x ^= label
    if x:
        raise ValueError("Center must have XOR zero")
    if len(center) == k + 1:
        return list(combinations(sorted(center), k))
    c = set(center)
    return [tuple(sorted((*center, x))) for x in range(n) if x not in c]


def graph6(adjacency: list[list[int]]) -> str:
    """Standard graph6 (upper triangle, j outermost) without newline."""
    n = len(adjacency)
    if n <= 62:
        header = chr(n + 63)
    elif n <= 258047:
        header = "~" + "".join(chr(63 + ((n >> shift) & 63)) for shift in (12, 6, 0))
    elif n < (1 << 36):
        header = "~~" + "".join(chr(63 + ((n >> shift) & 63)) for shift in (30, 24, 18, 12, 6, 0))
    else:
        raise ValueError("graph6 supports fewer than 2^36 vertices")
    neighbor_sets = [set(a) for a in adjacency]
    chars = []
    value = bits = 0
    for j in range(1, n):
        for i in range(j):
            value = (value << 1) | (j in neighbor_sets[i])
            bits += 1
            if bits == 6:
                chars.append(chr(63 + value))
                value = bits = 0
    if bits:
        chars.append(chr(63 + (value << (6 - bits))))
    return header + "".join(chars)


def instance(n: int, k: int, t: int) -> dict:
    vs, adj = graph(n, k, t)
    result: dict = {
        "parameters": {"n": n, "k": k, "t": t},
        "vertex_count": len(vs),
        "edge_count": sum(map(len, adj)) // 2,
        "vertices": vs,  # zero-based indices, lexicographic order
        "adjacency": adj,  # zero-based indices, sorted order
        "graph6": graph6(adj),
    }
    if n == 2 * k and n >= 2 and not n & (n - 1) and t == k - 1:
        centers = [xor_center(s, n) for s in vs]
        palette = sorted(set(centers))
        index = {center: i for i, center in enumerate(palette)}
        result["palette"] = palette
        result["colors"] = [index[center] for center in centers]
        result["chromatic_number"] = math.comb(n, k) // (k + 1)
    return result


def verify_instance(data: dict) -> dict:
    """Independently check every adjacency and every color fiber."""
    p = data["parameters"]
    n, k, t = p["n"], p["k"], p["t"]
    vs = [tuple(s) for s in data["vertices"]]
    assert vs == vertices(n, k)
    assert data["vertex_count"] == math.comb(n, k)
    adj = data["adjacency"]
    assert len(adj) == len(vs)
    assert all(a == sorted(set(a)) for a in adj)
    for j in range(len(vs)):
        assert j not in adj[j]
        for i in range(j):
            expected = is_edge(vs[i], vs[j], t)
            assert (i in adj[j]) == expected == (j in adj[i])
    assert data["edge_count"] == sum(map(len, adj)) // 2
    assert data["graph6"] == graph6(adj)
    if "colors" in data:
        colors = data["colors"]
        centers = [tuple(p) for p in data["palette"]]
        assert len(colors) == len(vs)
        assert len(centers) == data["chromatic_number"]
        groups = defaultdict(list)
        for i, (s, color) in enumerate(zip(vs, colors)):
            assert 0 <= color < len(centers)
            assert xor_center(s, n) == centers[color]
            groups[color].append(i)
        assert set(groups) == set(range(len(centers)))
        for color, members in groups.items():
            assert len(members) == k + 1
            assert set(vs[i] for i in members) == set(fiber(centers[color], n))
            assert all(j not in adj[i] for i, j in combinations(members, 2))
    return {"vertices": len(vs), "edges": data["edge_count"],
            "colors": len(data["palette"]) if "palette" in data else None,
            "status": "PASS"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=8)
    parser.add_argument("--k", type=int, default=4)
    parser.add_argument("--t", type=int, default=3)
    parser.add_argument("--max-vertices", type=int, default=1000,
                        help="safeguard against huge explicit graphs")
    parser.add_argument("--out", type=Path, default=Path(__file__).with_name("K8_4_3"),
                        help="output stem for .json and .g6")
    args = parser.parse_args()
    count = math.comb(args.n, args.k)
    if count > args.max_vertices:
        parser.error(f"{count} vertices; raise --max-vertices only if the explicit graph is needed")
    data = instance(args.n, args.k, args.t)
    report = verify_instance(data)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.with_suffix(".json").write_text(json.dumps(data, indent=2) + "\n")
    args.out.with_suffix(".g6").write_text(data["graph6"] + "\n")
    print(json.dumps(report))


if __name__ == "__main__":
    main()
