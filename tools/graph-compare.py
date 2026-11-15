# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
#
# Compares PILean's layered graph layout with Graphviz's `dot` by measures that do not depend on
# the eye: the number of edge pairs that cross, the total length of the edges, and the area of
# the drawing. `lake exe pilean-test --graph-quality DIR` (or the older `--graph-compare-out DIR`)
# writes, for each of a few graphs,
# DIR/<name>.dot (the graph with PILean's node sizes and gaps, and its clusters as `cluster`
# subgraphs) and DIR/<name>.layout (PILean's
# node boxes and edges flattened to polylines). This script runs `dot -Tplain` on each .dot,
# reads both layouts, flattens dot's Bézier splines the same way, and prints a table.
# Edges that share a node are not counted as crossing. Also prints the layout time of each (PILean's
# from DIR/<name>.time, with the load average at that moment; dot's measured here, wall clock) and,
# for each graph, the ratios of PILean to dot. Uses only the Python standard library
# and a `dot` program found on the path (nothing is installed or downloaded).
#
# Usage, from the repository root:
#   lake exe pilean-test --graph-quality /tmp/pilean-graphs
#   python3 -I tools/graph-compare.py /tmp/pilean-graphs [DOT]

import glob
import os
import shutil
import subprocess
import sys
import time

CELL = 64.0
SAMPLES = 12


def bezier(p0, p1, p2, p3, n=SAMPLES):
    """The points of a cubic Bézier at n + 1 equal parameter steps."""
    out = []
    for i in range(n + 1):
        t = i / n
        u = 1 - t
        out.append((
            u ** 3 * p0[0] + 3 * u * u * t * p1[0] + 3 * u * t * t * p2[0] + t ** 3 * p3[0],
            u ** 3 * p0[1] + 3 * u * u * t * p1[1] + 3 * u * t * t * p2[1] + t ** 3 * p3[1]))
    return out


def read_pilean(path):
    """(width, height, nodes {i: box}, edges [(src, dst, points)]) from a .layout file."""
    size = (0.0, 0.0)
    nodes = {}
    edges = []
    with open(path) as f:
        for line in f:
            w = line.split()
            if not w:
                continue
            if w[0] == "size":
                size = (float(w[1]), float(w[2]))
            elif w[0] == "node":
                nodes[int(w[1])] = tuple(float(x) for x in w[2:6])
            elif w[0] == "edge":
                n = int(w[4])
                vals = [float(x) for x in w[5:5 + 2 * n]]
                edges.append((int(w[2]), int(w[3]), list(zip(vals[0::2], vals[1::2]))))
    return size[0], size[1], nodes, edges


def read_dot(dot, path):
    """The same from `dot -Tplain` (inches, y upwards, converted to pixels, y downwards), and the
    seconds `dot` took."""
    t0 = time.monotonic()
    out = subprocess.run([dot, "-Tplain", path], capture_output=True, text=True, check=True)
    seconds = time.monotonic() - t0
    height = 0.0
    width = 0.0
    nodes = {}
    edges = []
    for line in out.stdout.splitlines():
        w = line.split()
        if not w:
            continue
        if w[0] == "graph":
            width, height = float(w[2]) * 72, float(w[3]) * 72
        elif w[0] == "node":
            i = int(w[1][1:])
            x, y, bw, bh = (float(v) * 72 for v in w[2:6])
            y = height - y
            nodes[i] = (x - bw / 2, y - bh / 2, x + bw / 2, y + bh / 2)
        elif w[0] == "edge":
            n = int(w[3])
            vals = [float(v) * 72 for v in w[4:4 + 2 * n]]
            pts = [(vals[2 * k], height - vals[2 * k + 1]) for k in range(n)]
            flat = [pts[0]]
            for k in range(0, n - 3, 3):
                flat.extend(bezier(pts[k], pts[k + 1], pts[k + 2], pts[k + 3])[1:])
            edges.append((int(w[1][1:]), int(w[2][1:]), flat))
    return (width, height, nodes, edges), seconds


def ccw(a, b, c):
    return (c[1] - a[1]) * (b[0] - a[0]) - (b[1] - a[1]) * (c[0] - a[0])


def cross(a, b, c, d):
    """Whether the segments ab and cd properly intersect."""
    return (ccw(a, c, d) > 0) != (ccw(b, c, d) > 0) and (ccw(a, b, c) > 0) != (ccw(a, b, d) > 0)


def crossing_pairs(edges):
    """The number of pairs of edges, not sharing a node, with intersecting segments."""
    cells = {}
    segs = []
    for k, (s, d, pts) in enumerate(edges):
        for a, b in zip(pts, pts[1:]):
            idx = len(segs)
            segs.append((k, a, b))
            x0, x1 = sorted((a[0], b[0]))
            y0, y1 = sorted((a[1], b[1]))
            for cx in range(int(x0 // CELL), int(x1 // CELL) + 1):
                for cy in range(int(y0 // CELL), int(y1 // CELL) + 1):
                    cells.setdefault((cx, cy), []).append(idx)
    seen = set()
    pairs = set()
    for members in cells.values():
        for i in range(len(members)):
            for j in range(i + 1, len(members)):
                p, q = members[i], members[j]
                if (p, q) in seen:
                    continue
                seen.add((p, q))
                kp, a, b = segs[p]
                kq, c, d = segs[q]
                if kp == kq or (min(kp, kq), max(kp, kq)) in pairs:
                    continue
                ep, eq = edges[kp], edges[kq]
                if {ep[0], ep[1]} & {eq[0], eq[1]}:
                    continue
                if cross(a, b, c, d):
                    pairs.add((min(kp, kq), max(kp, kq)))
    return len(pairs)


def metrics(layout):
    w, h, nodes, edges = layout
    length = sum(((b[0] - a[0]) ** 2 + (b[1] - a[1]) ** 2) ** 0.5
                 for _, _, pts in edges for a, b in zip(pts, pts[1:]))
    xs = [v for box in nodes.values() for v in (box[0], box[2])]
    ys = [v for box in nodes.values() for v in (box[1], box[3])]
    for _, _, pts in edges:
        xs += [p[0] for p in pts]
        ys += [p[1] for p in pts]
    area = (max(xs) - min(xs)) * (max(ys) - min(ys)) if xs else 0.0
    return crossing_pairs(edges), length, area, len(nodes), len(edges)


def main():
    if len(sys.argv) < 2:
        print(__doc__ if __doc__ else "usage: graph-compare.py DIR [DOT]")
        return 1
    directory = sys.argv[1]
    dot = sys.argv[2] if len(sys.argv) > 2 else shutil.which("dot")
    if not dot:
        print("no dot program found")
        return 1
    print(f"{'graph':16} {'nodes':>5} {'edges':>5} | {'':7} {'crossings':>9} "
          f"{'edge length':>12} {'area (px^2)':>13} {'layout ms':>9}")
    ratios = []
    for path in sorted(glob.glob(os.path.join(directory, "*.dot"))):
        name = os.path.basename(path)[:-4]
        ours = metrics(read_pilean(os.path.join(directory, name + ".layout")))
        layout, seconds = read_dot(dot, path)
        theirs = metrics(layout)
        try:
            with open(os.path.join(directory, name + ".time")) as f:
                ours_ms, load = f.read().split(None, 1)
                load = " ".join(load.strip("{} \n").split()[:3])
        except OSError:
            ours_ms, load = "?", ""
        for label, m, ms in (("PILean", ours, ours_ms), ("dot", theirs, f"{seconds * 1000:.0f}")):
            print(f"{name:16} {m[3]:5} {m[4]:5} | {label:7} {m[0]:9} {m[1]:12.0f} {m[2]:13.0f} "
                  f"{ms:>9}")
        ratios.append((name, ours, theirs, load))
    print()
    print(f"{'graph':16} {'crossings':>10} {'length':>8} {'area':>8}   (PILean / dot)")
    for name, o, t, load in ratios:
        r = lambda a, b: f"{a / b:8.2f}" if b else "     n/a"
        print(f"{name:16} {r(o[0], t[0]):>10} {r(o[1], t[1])} {r(o[2], t[2])}   load {load}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
