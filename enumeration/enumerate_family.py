#!/usr/bin/env python3
"""Enumerate the designs of Supplementary Methods M1 and check its counts.

The sites are the vertices (±1, ±1, ±1) of a cube and the nodes are the six
poles ±x, ±y, ±z; on each axis, a site is bonded to the pole whose sign matches
its coordinate. The script checks the counts of patterns, designs, and classes
stated in Section M1, the statements of Lemma M1.2, the remark that both
conditions are needed, the fact that the skeletons of 4a and 4b are only
two-connected, and the columns Environment, Order, Size, Vertices, and Edges of Table S3. It
needs only the Python standard library.
"""

from itertools import combinations, permutations, product

AXES = "xyz"
SITES = tuple(product((-1, 1), repeat=3))
NODES = tuple((a, s) for a in range(3) for s in (-1, 1))


def bonded(site, node):
    axis, sign = node
    return site[axis] == sign


NEIGHBOURS = {v: frozenset(c for c in NODES if bonded(v, c)) for v in SITES}
DIAGONALS = tuple((u, v) for u, v in combinations(SITES, 2)
                  if sum(a != b for a, b in zip(u, v)) == 1)


def node(name):
    return (AXES.index(name[1]), 1 if name[0] == "+" else -1)


PARALLEL = tuple((u, v) for u, v in DIAGONALS if u[2] != v[2])
SKEW = tuple((u, v) for u, v in DIAGONALS
             if (u[0] != v[0] and u[2] == -1) or (u[1] != v[1] and u[2] == 1))
TABLE_S3 = (
    # cage, pattern, deleted nodes, environment, order, size, vertices, edges
    ("1", (), (), 0, 48, 1, 14, 24),
    ("2a", PARALLEL, (), (0, 0), 16, 3, 14, 28),
    ("2b", SKEW, (), (0, 0), 8, 6, 14, 28),
    ("3", PARALLEL, ("+z",), (0, 1), 8, 6, 13, 24),
    ("4a", PARALLEL, ("+z", "-z"), (0, 2), 16, 3, 12, 20),
    ("4b", PARALLEL, ("+x", "-x"), (1, 0), 8, 6, 12, 20),
    ("4c", SKEW, ("+z", "-z"), (1, 0), 8, 6, 12, 20),
)


def design(pattern, deleted):
    return (frozenset(frozenset(e) for e in pattern), frozenset(deleted))


def molecules(pattern):
    covered = {v for e in pattern for v in e}
    return [frozenset((v,)) for v in SITES if v not in covered] + list(pattern)


def environment(molecule, deleted):
    if len(molecule) == 1:
        (v,) = molecule
        return len(NEIGHBOURS[v] & deleted)
    u, v = molecule
    return (len(NEIGHBOURS[u] & NEIGHBOURS[v] & deleted),
            len((NEIGHBOURS[u] ^ NEIGHBOURS[v]) & deleted))


def bonds_lost(molecule, deleted):
    return sum(len(NEIGHBOURS[v] & deleted) for v in molecule)


def skeleton(pattern, deleted):
    graph = {v: set(NEIGHBOURS[v] - deleted) for v in SITES}
    graph.update({c: {v for v in SITES if bonded(v, c)} for c in NODES if c not in deleted})
    for e in pattern:
        u, v = tuple(e)
        graph[u].add(v)
        graph[v].add(u)
    return graph


def connected(graph, removed=()):
    live = set(graph) - set(removed)
    start = next(iter(live))
    reached, pending = {start}, [start]
    while pending:
        for w in graph[pending.pop()] & live - reached:
            reached.add(w)
            pending.append(w)
    return reached == live


def cube_symmetries():
    """Permutations of the sites that carry every node's set of sites to a
    node's set, extended to the nodes."""
    sites_of = {frozenset(v for v in SITES if bonded(v, c)): c for c in NODES}
    result = []
    for images in permutations(SITES):
        s = dict(zip(SITES, images))
        moved = [frozenset(s[v] for v in group) for group in sites_of]
        if all(m in sites_of for m in moved):
            s.update(zip(sites_of.values(), (sites_of[m] for m in moved)))
            result.append(s)
    return result


def act(s, d):
    pattern, deleted = d
    return (frozenset(frozenset(s[v] for v in e) for e in pattern),
            frozenset(s[c] for c in deleted))


def main():
    patterns = [p for k in range(5) for p in combinations(DIAGONALS, k)
                if len({v for e in p for v in e}) == 2 * k]
    deletion_sets = [r for k in range(7) for r in combinations(NODES, k)]
    symmetries = cube_symmetries()
    assert len(DIAGONALS) == 12 and len(symmetries) == 48
    assert [sum(len(p) == k for p in patterns) for k in range(5)] == [1, 12, 42, 44, 9]
    assert len(patterns) == 108 and len(deletion_sets) == 64

    orbit = {}
    sets = {name: [] for name in ("all", "E", "D", "E and D",
                                  "bonds lost and D", "E and two deletions",
                                  "E and two bonds")}
    for p in patterns:
        for r in map(frozenset, deletion_sets):
            d = design(p, r)
            orbit[d] = frozenset(act(s, d) for s in symmetries)
            mols = molecules(d[0])
            graph = skeleton(d[0], r)
            uniform = len({environment(m, r) for m in mols}) == 1
            degree = min(map(len, graph.values())) >= 3
            sets["all"].append(d)
            if uniform:
                sets["E"].append(d)
                if len(r) <= 2:
                    sets["E and two deletions"].append(d)
                if all(len(NEIGHBOURS[v] - r) >= 2 for v in SITES):
                    sets["E and two bonds"].append(d)
            if degree:
                sets["D"].append(d)
                if len({(len(m), bonds_lost(m, r)) for m in mols}) == 1:
                    sets["bonds lost and D"].append(d)
            if uniform and degree:
                sets["E and D"].append(d)
                stabiliser = [s for s in symmetries if act(s, d) == d]
                assert len(r) <= 2 and connected(graph)
                assert {frozenset(s[v] for v in mols[0]) for s in stabiliser} == set(mols)

    classes = {name: len(set(orbit[d] for d in ds)) for name, ds in sets.items()}
    assert [len(sets[n]) for n in ("all", "E", "D", "E and D")] == [6912, 80, 273, 31]
    assert classes["all"] == 266 and classes["E and D"] == 7
    for name in ("bonds lost and D", "E and two deletions", "E and two bonds"):
        assert classes[name] == 8

    representatives = set()
    for cage, p, deleted, env, order, size, vertices, edges in TABLE_S3:
        r = frozenset(map(node, deleted))
        d = design(p, r)
        graph = skeleton(d[0], r)
        assert d in sets["E and D"]
        assert {environment(m, r) for m in molecules(d[0])} == {env}
        assert sum(act(s, d) == d for s in symmetries) == order
        assert len(orbit[d]) == size
        assert len(graph) == vertices and sum(map(len, graph.values())) == 2 * edges
        if cage in ("4a", "4b"):
            assert all(connected(graph, (x,)) for x in graph)
            assert not all(connected(graph, x) for x in combinations(graph, 2))
        representatives.add(orbit[d])
    assert len(representatives) == 7
    assert representatives == {orbit[d] for d in sets["E and D"]}

    print("patterns by number of diagonals: 1, 12, 42, 44, 9 (108 in all)")
    print("designs: 6912 in 266 classes; (E): 80; (D): 273; (E) and (D): 31 in 7 classes")
    print("checked: Lemma M1.2, the remark on both conditions, Table S3 without point groups")


if __name__ == "__main__":
    main()
