# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
#
# Compares PILean's layered graph layout with Graphviz's `dot` by measures that do not depend on
# the eye: the number of edge pairs that cross, the total length of the edges, and the area of
# the drawing; and by measures of what the eye objects to: how much an edge turns on average (the
# sum of the angles by which it changes direction), how often it changes from bending one way to
# bending the other, the length of the edges outside the box around the nodes, and the least
# distance between an edge and a node it does not end at. `lake exe pilean-test --graph-quality DIR` (or `--graph-compare-out DIR`)
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
#   python3 -I tools/graph-compare.py /tmp/pilean-graphs [DOT] [--tsv FILE] [--suffix S]
#
# With `--tsv FILE`, also writes dot's measures, one tab-separated row per graph (graph, nodes,
# edges, crossings, length, area, turning, inflections, outside, nearest) after a header row, to
# FILE; `--suffix S` appends S to every graph name there (`+packed` for a measurement made with
# components packed).

import glob
import math
import os
import shutil
import subprocess
import sys
import time

CELL = 64.0
SAMPLES = 12
# a bend of an edge counts from this many degrees
BEND = 5.0
# how far from an edge a node is looked for
REACH = 64.0


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


def turns(pts):
    """The signed turning angles (degrees) at the inner points of a polyline."""
    out = []
    prev = None
    for a, b in zip(pts, pts[1:]):
        d = (b[0] - a[0], b[1] - a[1])
        if d[0] * d[0] + d[1] * d[1] < 1e-12:
            continue
        if prev is not None:
            out.append(math.degrees(math.atan2(prev[0] * d[1] - prev[1] * d[0],
                                               prev[0] * d[0] + prev[1] * d[1])))
        prev = d
    return out


def inflections(angles, least=BEND):
    """How often a polyline changes from bending one way to bending the other; a bend counts
    when it turns by `least` degrees or more in all."""
    bends = 0
    sign = 0
    total = 0.0
    for a in angles:
        s = (a > 0) - (a < 0)
        if s == 0:
            continue
        if s != sign:
            if total >= least:
                bends += 1
            sign = s
            total = 0.0
        total += abs(a)
    if total >= least:
        bends += 1
    return max(0, bends - 1)


def inside_length(a, b, box):
    """The length of the part of the segment ab inside the box (Liang and Barsky)."""
    dx, dy = b[0] - a[0], b[1] - a[1]
    t0, t1 = 0.0, 1.0
    for p, q in ((-dx, a[0] - box[0]), (dx, box[2] - a[0]), (-dy, a[1] - box[1]),
                 (dy, box[3] - a[1])):
        if p == 0:
            if q < 0:
                return 0.0
        else:
            r = q / p
            if p < 0:
                t0 = max(t0, r)
            else:
                t1 = min(t1, r)
    return max(0.0, t1 - t0) * math.hypot(dx, dy)


def segment_box_distance(a, b, box):
    """The distance between the segment ab and the box (0 when they meet)."""
    if inside_length(a, b, box) > 0 or (box[0] <= a[0] <= box[2] and box[1] <= a[1] <= box[3]):
        return 0.0

    def point_segment(p, c, d):
        vx, vy = d[0] - c[0], d[1] - c[1]
        l2 = vx * vx + vy * vy
        t = 0.0 if l2 == 0 else max(0.0, min(1.0, ((p[0] - c[0]) * vx + (p[1] - c[1]) * vy) / l2))
        return math.hypot(p[0] - c[0] - t * vx, p[1] - c[1] - t * vy)

    def point_box(p):
        return math.hypot(max(box[0] - p[0], 0.0, p[0] - box[2]),
                          max(box[1] - p[1], 0.0, p[1] - box[3]))

    corners = ((box[0], box[1]), (box[2], box[1]), (box[2], box[3]), (box[0], box[3]))
    return min(min(point_segment(c, a, b) for c in corners), point_box(a), point_box(b))


def eye(layout):
    """What the eye objects to in a drawing: the mean turning of an edge (degrees) and its mean
    number of inflections, the length of the edges outside the box around the nodes, and the
    least distance between an edge and a node it does not end at (looked for up to REACH)."""
    _, _, nodes, edges = layout
    if not nodes or not edges:
        return 0.0, 0.0, 0.0, REACH
    hull = (min(b[0] for b in nodes.values()), min(b[1] for b in nodes.values()),
            max(b[2] for b in nodes.values()), max(b[3] for b in nodes.values()))
    cells = {}
    for i, b in nodes.items():
        for cx in range(int((b[0] - REACH) // CELL), int((b[2] + REACH) // CELL) + 1):
            for cy in range(int((b[1] - REACH) // CELL), int((b[3] + REACH) // CELL) + 1):
                cells.setdefault((cx, cy), []).append(i)
    turning = 0.0
    bends = 0
    outside = 0.0
    nearest = REACH
    for s, d, pts in edges:
        angles = turns(pts)
        turning += sum(abs(a) for a in angles)
        bends += inflections(angles)
        for a, b in zip(pts, pts[1:]):
            outside += math.hypot(b[0] - a[0], b[1] - a[1]) - inside_length(a, b, hull)
            if s == d:
                continue
            x0, x1 = sorted((a[0], b[0]))
            y0, y1 = sorted((a[1], b[1]))
            seen = set()
            for cx in range(int(x0 // CELL), int(x1 // CELL) + 1):
                for cy in range(int(y0 // CELL), int(y1 // CELL) + 1):
                    for i in cells.get((cx, cy), ()):
                        if i != s and i != d and i not in seen:
                            seen.add(i)
                            nearest = min(nearest, segment_box_distance(a, b, nodes[i]))
    return turning / len(edges), bends / len(edges), outside, nearest


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
    args = sys.argv[1:]
    options = {}
    for flag in ("--tsv", "--suffix"):
        if flag in args:
            i = args.index(flag)
            if i + 1 >= len(args):
                print(f"{flag} needs a value")
                return 1
            options[flag] = args[i + 1]
            del args[i:i + 2]
    directory = args[0]
    dot = args[1] if len(args) > 1 else shutil.which("dot")
    if not dot:
        print("no dot program found")
        return 1
    print(f"{'graph':16} {'nodes':>5} {'edges':>5} | {'':7} {'crossings':>9} "
          f"{'edge length':>12} {'area (px^2)':>13} {'layout ms':>9}")
    ratios = []
    recorded = []
    eyes = []
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
        recorded.append((name + options.get("--suffix", ""), theirs, eye(layout)))
        eyes.append((name, eye(read_pilean(os.path.join(directory, name + ".layout"))),
                     recorded[-1][2]))
    print()
    print(f"{'graph':16} {'crossings':>10} {'length':>8} {'area':>8}   (PILean / dot)")
    for name, o, t, load in ratios:
        r = lambda a, b: f"{a / b:8.2f}" if b else "     n/a"
        print(f"{name:16} {r(o[0], t[0]):>10} {r(o[1], t[1])} {r(o[2], t[2])}   load {load}")
    print()
    print(f"{'graph':16} | {'':7} {'turning':>8} {'inflections':>11} {'outside':>10} {'nearest':>8}"
          "   (degrees and count per edge, pixels, pixels)")
    for name, o, t in eyes:
        for label, e in (("PILean", o), ("dot", t)):
            print(f"{name:16} | {label:7} {e[0]:8.1f} {e[1]:11.2f} {e[2]:10.0f} {e[3]:8.1f}")
    if "--tsv" in options:
        with open(options["--tsv"], "w") as f:
            f.write("graph\tnodes\tedges\tcrossings\tlength\tarea\tturning\tinflections\toutside"
                    "\tnearest\n")
            for name, m, e in recorded:
                f.write(f"{name}\t{m[3]}\t{m[4]}\t{m[0]}\t{m[1]:.0f}\t{m[2]:.0f}\t{e[0]:.1f}"
                        f"\t{e[1]:.2f}\t{e[2]:.0f}\t{e[3]:.1f}\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
