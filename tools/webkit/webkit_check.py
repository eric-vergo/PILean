# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
"""The position checks of motions in WebKit, the engine of Safari (macOS only, optional):

    python3 tools/webkit/webkit_check.py DIR [--runner PATH]

DIR holds animated SVG files with their expectations, as `lake exe pilean-test --motion-out DIR`
and a site's own writer (`example-test --motion-out DIR`) write them: every `<name>.json` with its
`<name>.svg` is checked (expectations in another format than 3, `FORMAT`, fail, saying which
format was found). Each file is opened in the system's WebKit by `runner.swift` (compiled once
with the system's `swiftc` into a folder of the temporary directory named after the source's
hash, unless `--runner` names a built one), which loads files below DIR only and reaches no
network, in a transparent click-through window (see `runner.swift` for exactly what it does to the
desktop; it needs a logged-in session with a screen, and is not for a Linux CI); its home is a
temporary folder, so nothing is written into the user's Library. `runner_test.py` shows the runner's
limits hold. Checked, for every motion:

* the clock runs: read twice 0.3 s apart it has advanced, and it gets past two cycles; otherwise
  the motion fails (WebKit stops the clock of a picture in no window, which would make every
  check below pass on a still picture);
* with the clock paused and set, in the first loop and again one cycle later: every actor where
  its key's still has it at the middle of every rest, on its circle at the eased angle at a
  quarter, a half and three quarters of every turn, on its segment at the eased fraction at the
  same times of every slide, the panels of a picture of panels in phase, labels and markers
  upright (the tolerances of `tools/motion-browser-check.py`); and at every sample of every
  appearance and disappearance (the expectations' `opacities`) the layer of its actor at the
  expected opacity within 0.02 (`OPACITY_TOL`), read as the product of the computed opacity of the
  layer and of each ancestor up to the root. WebKit puts the value of a SMIL animation of the
  `opacity` attribute in the computed style, and draws it: measured once on the golden motions
  with a snapshot of the `WKWebView` (which this runner does not take), the drawn opacity is
  within 0.002 of the expected one, the computed one within 3e-6. Every listed sample must be
  read, and each line says how many were;
* free-running over the first two loops, read every 30 ms or so: near the middle of every rest long
  enough to be read so (within 0.1 s of its middle and at least the readings' jitter, the 95th
  percentile of the times between readings (36 ms measured, the longest gap reported too), inside
  the part of the rest in which the key is shown still: a reading's clock and the frame it reads can
  be one interval between readings apart, so a rest whose still part is not longer than twice that
  jitter plus 0.02 s is not read free-running; the paused readings hold every rest) every actor
  where its key's still has it, and inside every turn and every slide the actor on its circle or its
  segment; the line names the jitter and the rests read; each kind of reading must
  have been made in both loops, so none passes for want of readings, and a motion with no rest
  long enough fails as undecided.

A key that is not a still has a rest like every key, and is checked like every key. The opacity
check is shown to catch a mark whose fade never starts: in the page of the first motion that
lists opacities, after its readings, the opacity animation of the group nearest the first entry's
layer is held at 0 and the samples are read again; some must be off ("caught"), or the run fails.
The last line gives the motions that hold, the opacity samples asserted and the mutation's
verdict.

A motion with no anchored actor (a morph alone) has no position to check here: it is reported as
"positions not checked" (`clock only`), not as holding; `tools/motion-browser-check.py` checks
such a motion by its pixels against its stills and by its decided switch probe.

Exit status 0 when no motion fails, 1 otherwise, 2 when it cannot run (not macOS, no `swiftc`).
"""

import json
import math
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
REST_TOL = 0.05
RADIUS_TOL = 0.05
ANGLE_TOL = 0.5
UPRIGHT_TOL = 0.01
OPACITY_TOL = 0.02
# how near the middle of a rest a free-running reading counts as one of the rest (seconds)
NEAR_REST = 0.1
# The least time a free-running reading must keep from both ends of the part of a rest in which
# its key is shown still, beyond the readings' jitter (seconds): a rest is read free-running only
# when that part is longer than twice the jitter plus twice this (`readable_rests`).
REST_MARGIN = 0.01

SCRIPT = r"""
const svg = document.documentElement;
const sleep = ms => new Promise(r => setTimeout(r, ms));
const at = (m, x, y) => [m.a * x + m.c * y + m.e, m.b * x + m.d * y + m.f];
const read = () => {
  const actors = [], uprights = [];
  for (const g of svg.querySelectorAll('[data-pilean-actor]')) {
    const [x, y] = g.getAttribute('data-pilean-anchor').split(' ').map(Number);
    actors.push([g.getAttribute('data-pilean-actor'), at(g.getCTM(), x, y)]);
  }
  for (const g of svg.querySelectorAll('[data-pilean-upright]')) {
    const m = g.getCTM();
    uprights.push(Math.atan2(m.b, m.a) * 180 / Math.PI);
  }
  return {t: svg.getCurrentTime(), actors, uprights};
};
const t0 = svg.getCurrentTime();
await sleep(300);
const t1 = svg.getCurrentTime();
const free = [];
if (t1 > t0) {
  const end = 2 * SPEC.cycle + 0.2;
  while (svg.getCurrentTime() < end) {
    free.push(read());
    await sleep(30);
  }
}
svg.pauseAnimations();
const seek = [];
for (const loop of [0, 1])
  for (const t of TIMES) {
    svg.setCurrentTime(t + loop * SPEC.cycle);
    await sleep(5);
    seek.push(Object.assign(read(), {want: t, loop}));
  }
// the opacity a reader sees of the nth layer of an actor: the product of the computed opacity of
// the element and of each of its ancestors up to the root (`null` when there is no such element)
const layer = (id, nth) => [...svg.querySelectorAll('[data-pilean-actor]')]
  .filter(e => e.getAttribute('data-pilean-actor') === id)[nth];
const opacity = (id, nth) => {
  const el = layer(id, nth);
  if (!el) return null;
  let o = 1;
  for (let e = el; e; e = e.parentElement) {
    o *= parseFloat(getComputedStyle(e).opacity);
    if (e === svg) break;
  }
  return o;
};
const fades = async () => {
  const out = [];
  for (const loop of [0, 1])
    SPEC.opacities.forEach((e, entry) => e.samples.forEach(s => out.push([entry, s, loop])));
  const read = [];
  for (const [entry, s, loop] of out) {
    svg.setCurrentTime(s.t + loop * SPEC.cycle);
    await sleep(5);
    const e = SPEC.opacities[entry];
    read.push({entry, t: s.t, loop, o: opacity(e.id, e.nth)});
  }
  return read;
};
const opacities = await fades();
// the mutation: the opacity animation of the group nearest the first entry's layer held at 0
let mutated = null, shifted = null;
if (MUTATE && SPEC.opacities.length) {
  const e = SPEC.opacities[0];
  let fade = null;
  for (let g = layer(e.id, e.nth); g && g !== svg && !fade; g = g.parentElement)
    fade = [...g.children].find(c =>
      c.localName === 'animate' && c.getAttribute('attributeName') === 'opacity');
  if (fade) {
    const kept = fade.getAttribute('values');
    fade.setAttribute('values', kept.split(';').map(() => '0').join(';'));
    mutated = await fades();
    // the same fade one boundary late: the mark shows at the wrong time
    const v = kept.split(';');
    fade.setAttribute('values', [v[0], ...v.slice(0, -1)].join(';'));
    shifted = await fades();
    fade.setAttribute('values', kept);
  }
}
return JSON.stringify({ua: navigator.userAgent, t0, t1, free, seek, opacities, mutated, shifted});
"""


# The version of the expectations' format this check reads (`PILeanTest.MotionChecks
# .expectationsFormat`).
FORMAT = 3


def spec_problem(spec):
    """Why the expectations cannot be checked (`tools/motion-browser-check.py`, the same rule):
    another format than `FORMAT`, or other turns or slides than the motion declares."""
    if spec.get("format", 1) != FORMAT or "declared" not in spec or "slides" not in spec or \
            "opacities" not in spec or \
            any(k not in r for r in spec["rests"] for k in ("from", "until", "still")):
        return (f"the expectations are in format {spec.get('format', 1)}, this check reads format "
                f"{FORMAT} (rests with their ends and whether they are stills, slides, "
                "opacities): rebuild the expectations writer with this version of PILean")
    d = spec["declared"]
    if d["turns"] != len(spec["turns"]) or d["slides"] != len(spec["slides"]):
        return (f"the motion declares {d['turns']} turns and {d['slides']} slides, the "
                f"expectations list {len(spec['turns'])} and {len(spec['slides'])}")
    return None


def listed_opacities(root, name):
    """Whether the expectations of `name` can be read and list opacities."""
    with open(os.path.join(root, name + ".json")) as f:
        spec = json.load(f)
    return not spec_problem(spec) and bool(spec["opacities"])


def first(actors, ident):
    for name, xy in actors:
        if name == ident:
            return xy
    return None


def wrap(deg):
    return (deg + 180) % 360 - 180


def build_runner():
    """The runner compiled from `runner.swift`: kept in one folder of the temporary directory,
    named after the SHA-256 of the source, and compiled only when it is not there."""
    import hashlib
    src = os.path.join(HERE, "runner.swift")
    with open(src, "rb") as f:
        digest = hashlib.sha256(f.read()).hexdigest()[:16]
    out = os.path.join(tempfile.gettempdir(), f"pilean-webkit-runner-{digest}", "runner")
    if not os.path.exists(out):
        os.makedirs(os.path.dirname(out), exist_ok=True)
        subprocess.run(["swiftc", "-O", "-o", out + ".new", src], check=True,
                       stdout=subprocess.DEVNULL, timeout=600)
        os.replace(out + ".new", out)
    return out


def run_page(runner, root, path, script, width, height, timeout):
    """Runs `script` in the page `path` (below `root`) in WebKit; the runner's stdout, or an
    `ERROR` line. The runner's home is a temporary folder (`CFFIXED_USER_HOME`), removed after,
    so that nothing is written into the user's Library."""
    import shutil
    # named after this process, so that a later runner can remove it if this run is killed
    home = tempfile.mkdtemp(prefix=f"pilean-webkit-home-{os.getpid()}-")
    env = dict(os.environ, WEBKIT_TIMEOUT=str(int(timeout)), CFFIXED_USER_HOME=home)
    try:
        url = "file://" + os.path.abspath(path)
        r = subprocess.run([runner, os.path.abspath(root), url, script, str(width), str(height)],
                           capture_output=True, text=True, env=env, timeout=timeout + 30)
        return r.stdout.strip() or f"ERROR runner: {r.stderr.strip()[:200]}"
    except subprocess.TimeoutExpired:
        return f"ERROR the runner did not end within {timeout + 30:.0f} s"
    finally:
        shutil.rmtree(home, ignore_errors=True)


def times_of(spec):
    """Every moment the expectations name: rests, turns' and slides' samples, panels' phase."""
    ts = [r["t"] for r in spec["rests"]]
    ts += [s["t"] for k in ("turns", "slides") for m in spec.get(k, []) for s in m["samples"]]
    ts += [p["t"] for p in spec.get("phase", [])]
    return sorted(set(ts))


def seek_errors(spec, reads):
    """The largest errors of the paused readings, by kind, over both loops."""
    by_t = {}
    for r in reads:
        by_t[(r["loop"], round(r["want"], 6))] = r
    err = {"rest": 0.0, "radius": 0.0, "angle": 0.0, "slide": 0.0, "phase": 0.0, "upright": 0.0}
    missing = []
    for loop in (0, 1):
        def seen(t):
            return by_t[(loop, round(t, 6))]
        for rest in spec["rests"]:
            r = seen(rest["t"])
            for a in rest["actors"]:
                xy = first(r["actors"], a["id"])
                if xy is None:
                    missing.append(a["id"])
                else:
                    err["rest"] = max(err["rest"], math.dist(xy, a["at"]))
        for turn in spec["turns"]:
            c, s = turn["centre"], turn["start"]
            rad = math.dist(s, c)
            a0 = math.degrees(math.atan2(s[1] - c[1], s[0] - c[0]))
            for sm in turn["samples"]:
                xy = first(seen(sm["t"])["actors"], turn["id"])
                if xy is None:
                    missing.append(turn["id"])
                    continue
                err["radius"] = max(err["radius"], abs(math.dist(xy, c) - rad))
                if rad >= 1:
                    a = math.degrees(math.atan2(xy[1] - c[1], xy[0] - c[0]))
                    err["angle"] = max(err["angle"], abs(wrap((a - a0) - turn["sweep"] * sm["f"])))
        for sl in spec.get("slides", []):
            a, b = sl["from"], sl["to"]
            for sm in sl["samples"]:
                xy = first(seen(sm["t"])["actors"], sl["id"])
                if xy is None:
                    missing.append(sl["id"])
                    continue
                f = sm["f"]
                err["slide"] = max(err["slide"], math.dist(
                    xy, [a[0] + f * (b[0] - a[0]), a[1] + f * (b[1] - a[1])]))
        for ph in spec.get("phase", []):
            got = dict((i, xy) for i, xy in seen(ph["t"])["actors"])
            for ident, want in ph["actors"]:
                if ident not in got:
                    missing.append(ident)
                else:
                    err["phase"] = max(err["phase"], math.dist(got[ident], want))
        for r in reads:
            err["upright"] = max([err["upright"]] + [abs(u) for u in r["uprights"]])
    return err, missing


def on_segment(p, a, b):
    """The distance from `p` to the segment from `a` to `b`."""
    dx, dy = b[0] - a[0], b[1] - a[1]
    n = dx * dx + dy * dy
    f = 0 if n == 0 else max(0.0, min(1.0, ((p[0] - a[0]) * dx + (p[1] - a[1]) * dy) / n))
    return math.dist(p, [a[0] + f * dx, a[1] + f * dy])


def jitter(reads):
    """The readings' jitter (seconds), and the longest gap: the 95th percentile and the largest of
    the times between two consecutive free-running readings. A reading's clock and the drawing it
    reads may be a whole interval apart (the drawing is of the last frame painted), so a reading
    is trusted to show a rest only that far inside it; the percentile, so that one stall does not
    make every rest too short to read (a reading in a stall that lands outside its rest's still
    part shows as an error, not as a pass)."""
    ts = [r["t"] for r in reads]
    gaps = sorted(b - a for a, b in zip(ts, ts[1:]))
    if not gaps:
        return 0.0, 0.0
    return gaps[min(len(gaps) - 1, int(0.95 * len(gaps)))], gaps[-1]


def readable_rests(spec, j):
    """The rests whose still part is long enough to be read free-running with the jitter `j`:
    half of it longer than `j + REST_MARGIN`; each with the distance from its middle within which
    a reading counts (`NEAR_REST` at most)."""
    out = []
    for rest in spec["rests"]:
        half = (rest["until"] - rest["from"]) / 2
        if half > j + REST_MARGIN:
            out.append((rest, min(NEAR_REST, half - j)))
    return out


def free_errors(spec, reads):
    """The largest errors of the free-running readings by kind, how many readings of each kind
    each loop had, the readings' jitter and the keys of the rests read (`readable_rests`)."""
    cycle = spec["cycle"]
    err = {"rest": 0.0, "turn": 0.0, "slide": 0.0}
    counts = {(k, loop): 0 for k in err for loop in (0, 1)}
    j, longest = jitter(reads)
    rests = readable_rests(spec, j)
    for r in reads:
        loop = int(r["t"] // cycle)
        if loop > 1:
            continue
        t = r["t"] % cycle
        for rest, near in rests:
            # well inside the part of the rest in which the key is shown still
            if abs((t - rest["t"] + cycle / 2) % cycle - cycle / 2) <= near:
                counts[("rest", loop)] += 1
                for a in rest["actors"]:
                    xy = first(r["actors"], a["id"])
                    err["rest"] = max(err["rest"], math.inf if xy is None else
                                      math.dist(xy, a["at"]))
        for turn in spec["turns"]:
            lo, hi = turn["samples"][0]["t"], turn["samples"][-1]["t"]
            if lo <= t <= hi:
                counts[("turn", loop)] += 1
                xy = first(r["actors"], turn["id"])
                c, s = turn["centre"], turn["start"]
                err["turn"] = max(err["turn"], math.inf if xy is None else
                                  abs(math.dist(xy, c) - math.dist(s, c)))
        for sl in spec.get("slides", []):
            lo, hi = sl["samples"][0]["t"], sl["samples"][-1]["t"]
            if lo <= t <= hi:
                counts[("slide", loop)] += 1
                xy = first(r["actors"], sl["id"])
                err["slide"] = max(err["slide"], math.inf if xy is None else
                                   on_segment(xy, sl["from"], sl["to"]))
    return err, counts, (j, longest), [rest["key"] for rest, _ in rests]


def opacity_errors(spec, reads):
    """The largest difference between the opacities read and the expected ones, how many samples
    were read, and how many were off by more than `OPACITY_TOL`."""
    err, read, off = 0.0, 0, 0
    for r in reads or []:
        if r["o"] is None:
            continue
        want = next(s["o"] for s in spec["opacities"][r["entry"]]["samples"] if s["t"] == r["t"])
        read += 1
        err = max(err, abs(r["o"] - want))
        off += abs(r["o"] - want) > OPACITY_TOL
    return err, read, off


def check(runner, root, name, mutate=False):
    """The checks of the module docstring on the motion `name`; with `mutate`, also the opacity
    mutation in its page. Returns the verdict (`ok`, `clock only` or `FAILED`), the number of
    opacity samples asserted, and with `mutate` whether the mutation was caught."""
    with open(os.path.join(root, name + ".json")) as f:
        spec = json.load(f)
    why = spec_problem(spec)
    if why:
        print(f"{name}: {why} -> FAILED")
        return "FAILED", 0, None
    prelude = (f"const SPEC = {json.dumps(spec)};\nconst TIMES = {json.dumps(times_of(spec))};\n"
               f"const MUTATE = {'true' if mutate else 'false'};\n")
    with tempfile.NamedTemporaryFile("w", suffix=".js", delete=False) as f:
        f.write(prelude + SCRIPT)
        script = f.name
    out = run_page(runner, root, os.path.join(root, spec["svg"]), script, 800, 1000,
                   2 * spec["cycle"] + 60)
    os.unlink(script)
    if not out.startswith("{"):
        print(f"{name}: WebKit did not run the check: {out[:200]} -> FAILED")
        return "FAILED", 0, None
    r = json.loads(out)
    runs = r["t1"] > r["t0"] and bool(r["free"]) and r["free"][-1]["t"] >= 2 * spec["cycle"]
    seek, missing = seek_errors(spec, r["seek"])
    free, counts, jit, read_keys = free_errors(spec, r["free"])
    kinds = ["rest"] + (["turn"] if spec["turns"] else []) + \
        (["slide"] if spec.get("slides") else [])
    vacuous = [f"{k} in loop {loop + 1}" for k in kinds for loop in (0, 1)
               if counts[(k, loop)] == 0]
    listed = 2 * sum(len(e["samples"]) for e in spec["opacities"])
    o_err, o_read, o_off = opacity_errors(spec, r["opacities"])
    caught = None
    if mutate:
        _, m_read, m_off = opacity_errors(spec, r["mutated"])
        _, s_read, s_off = opacity_errors(spec, r["shifted"] or [])
        caught = m_off > 0 and s_off > 0
        print(f"opacity mutation (fade-never-starts): in {name} the fade of "
              f"{spec['opacities'][0]['id']} never starts (its group's opacity animation held at "
              f"0): {m_off} of {m_read} samples off -> "
              f"{'caught' if m_off > 0 else 'NOT CAUGHT, FAILED'}")
        print(f"opacity mutation (window-shifted): its values one boundary later, the mark shown "
              f"at the wrong time: {s_off} of {s_read} samples off -> "
              f"{'caught' if s_off > 0 else 'NOT CAUGHT, FAILED'}")
    ok = (runs and not missing and not vacuous and o_read == listed and o_off == 0
          and o_err <= OPACITY_TOL and seek["rest"] <= REST_TOL
          and seek["radius"] <= RADIUS_TOL and seek["angle"] <= ANGLE_TOL
          and seek["slide"] <= REST_TOL and seek["phase"] <= REST_TOL
          and seek["upright"] <= UPRIGHT_TOL and free["rest"] <= REST_TOL
          and free["turn"] <= RADIUS_TOL and free["slide"] <= REST_TOL)
    # a motion with no anchored actor (a morph alone) has nothing here to hold to a position
    anchored = any(rest["actors"] for rest in spec["rests"])
    print(f"{name}: clock {r['t0']:.2f} -> {r['t1']:.2f} s and on to "
          f"{(r['free'][-1]['t'] if r['free'] else 0):.2f} s (cycle {spec['cycle']} s); paused, "
          f"both loops: rests {seek['rest']:.2e} px, arcs {seek['radius']:.2e} px and "
          f"{seek['angle']:.2e} deg, slides {seek['slide']:.2e} px, phase {seek['phase']:.2e} px, "
          f"uprights {seek['upright']:.2e} deg, opacities {o_err:.2e} over {o_read} of {listed} "
          f"samples; free-running, {len(r['free'])} readings (jitter {jit[0] * 1000:.0f} ms, the "
          f"95th percentile of the gaps, the longest {jit[1] * 1000:.0f} ms; rests "
          f"read: keys {read_keys}): rests "
          f"{free['rest']:.2e} px, on the circle {free['turn']:.2e} px, on the segment "
          f"{free['slide']:.2e} px"
          + ("" if read_keys else "; UNDECIDED: no rest is long enough to be read free-running "
             f"(its still part must be longer than {2 * (jit[0] + REST_MARGIN):.3f} s)")
          + (f"; missing {sorted(set(missing))[:3]}" if missing else "")
          + (f"; no readings of {', '.join(vacuous)}" if vacuous else "")
          + ("" if runs else "; THE CLOCK DID NOT RUN")
          + ("" if anchored or not ok else "; positions not checked: no anchored actor (a "
             "morph is checked by motion-browser-check.py, its pixels and its probe)")
          + f" -> {'FAILED' if not ok else 'ok' if anchored else 'clock only'}")
    return ("ok" if ok and anchored else "clock only" if ok else "FAILED"), o_read, caught


def main(argv):
    if sys.platform != "darwin":
        print("webkit_check: macOS only; nothing checked")
        return 2
    args = list(argv)
    runner = None
    if "--runner" in args:
        i = args.index("--runner")
        runner = args[i + 1]
        del args[i:i + 2]
    if len(args) != 1:
        print("usage: python3 tools/webkit/webkit_check.py DIR [--runner PATH]")
        return 2
    root = args[0]
    try:
        runner = runner or build_runner()
    except (OSError, subprocess.CalledProcessError) as e:
        print(f"webkit_check: cannot build the runner ({e}); nothing checked")
        return 2
    names = sorted(f[:-5] for f in os.listdir(root) if f.endswith(".json"))
    if not names:
        print(f"webkit_check: no motions in {root}")
        return 1
    # the opacity mutation runs in the page of the first motion whose expectations list opacities
    target = next((n for n in names if listed_opacities(root, n)), None)
    results = [check(runner, root, n, mutate=n == target) for n in names]
    verdicts = [v for v, _, _ in results]
    failures = verdicts.count("FAILED")
    only = verdicts.count("clock only")
    caught = next((c for n, (_, _, c) in zip(names, results) if n == target), None)
    if target is None:
        print("opacity mutation: no motion lists opacities -> FAILED")
    print(f"webkit: {len(names) - failures - only} of {len(names)} motions hold"
          + (f", {only} with positions not checked (no anchored actor; their clock runs)"
             if only else "") + (f", {failures} failed" if failures else "")
          + f"; {sum(n for _, n, _ in results)} opacity samples asserted; the opacity mutation "
          + ("caught" if caught else "NOT CAUGHT"))
    return 1 if failures or not caught else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
