# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
"""The position checks of motions in WebKit, the engine of Safari (macOS only, optional):

    python3 tools/webkit/webkit_check.py DIR [--runner PATH]

DIR holds animated SVG files with their expectations, as `lake exe pilean-test --motion-out DIR`
and a site's own writer (`example-test --motion-out DIR`) write them: every `<name>.json` with its
`<name>.svg` is checked (expectations of an older format fail). Each file is opened in the
system's WebKit by `runner.swift` (compiled once with the system's `swiftc` into a folder of the
temporary directory named after the source's hash, unless `--runner` names a built one), which
loads files below DIR only and reaches no network, in a transparent click-through window (see
`runner.swift` for exactly what it does to the desktop; it needs a logged-in session with a
screen, and is not for a Linux CI); its home is a temporary folder, so nothing is written into
the user's Library. `runner_test.py` shows the runner's limits hold. Checked, for every motion:

* the clock runs: read twice 0.3 s apart it has advanced, and it gets past two cycles; otherwise
  the motion fails (WebKit stops the clock of a picture in no window, which would make every
  check below pass on a still picture);
* with the clock paused and set, in the first loop and again one cycle later: every actor where
  its key's still has it at the middle of every rest, on its circle at the eased angle at a
  quarter, a half and three quarters of every turn, on its segment at the eased fraction at the
  same times of every slide, the panels of a picture of panels in phase, labels and markers
  upright (the tolerances of `tools/motion-browser-check.py`);
* free-running over the first two loops, read every 30 ms or so: near the middle of every rest
  every actor where its key's still has it, and inside every turn and every slide the actor on its
  circle or its segment; each kind of reading must have been made in both loops, so none passes
  for want of readings.

Exit status 0 when every motion holds, 1 otherwise, 2 when it cannot run (not macOS, no `swiftc`).
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
# how near the middle of a rest a free-running reading counts as one of the rest (seconds)
NEAR_REST = 0.1

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
return JSON.stringify({ua: navigator.userAgent, t0, t1, free, seek});
"""


def spec_problem(spec):
    """Why the expectations cannot be checked (`tools/motion-browser-check.py`, the same rule):
    an older format, or other turns or slides than the motion declares."""
    if spec.get("format", 1) < 2 or "declared" not in spec or "slides" not in spec or \
            any("from" not in r for r in spec["rests"]):
        return (f"the expectations are in format {spec.get('format', 1)}, this check reads format "
                "2: rebuild the expectations writer with this version of PILean")
    d = spec["declared"]
    if d["turns"] != len(spec["turns"]) or d["slides"] != len(spec["slides"]):
        return (f"the motion declares {d['turns']} turns and {d['slides']} slides, the "
                f"expectations list {len(spec['turns'])} and {len(spec['slides'])}")
    return None


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
    home = tempfile.mkdtemp(prefix="pilean-webkit-home-")
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


def free_errors(spec, reads):
    """The largest errors of the free-running readings by kind, and how many readings of each
    kind each loop had."""
    cycle = spec["cycle"]
    err = {"rest": 0.0, "turn": 0.0, "slide": 0.0}
    counts = {(k, loop): 0 for k in err for loop in (0, 1)}
    for r in reads:
        loop = int(r["t"] // cycle)
        if loop > 1:
            continue
        t = r["t"] % cycle
        for rest in spec["rests"]:
            if abs((t - rest["t"] + cycle / 2) % cycle - cycle / 2) <= NEAR_REST:
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
    return err, counts


def check(runner, root, name):
    with open(os.path.join(root, name + ".json")) as f:
        spec = json.load(f)
    why = spec_problem(spec)
    if why:
        print(f"{name}: {why} -> FAILED")
        return False
    prelude = f"const SPEC = {json.dumps(spec)};\nconst TIMES = {json.dumps(times_of(spec))};\n"
    with tempfile.NamedTemporaryFile("w", suffix=".js", delete=False) as f:
        f.write(prelude + SCRIPT)
        script = f.name
    out = run_page(runner, root, os.path.join(root, spec["svg"]), script, 800, 1000,
                   2 * spec["cycle"] + 60)
    os.unlink(script)
    if not out.startswith("{"):
        print(f"{name}: WebKit did not run the check: {out[:200]} -> FAILED")
        return False
    r = json.loads(out)
    runs = r["t1"] > r["t0"] and bool(r["free"]) and r["free"][-1]["t"] >= 2 * spec["cycle"]
    seek, missing = seek_errors(spec, r["seek"])
    free, counts = free_errors(spec, r["free"])
    kinds = ["rest"] + (["turn"] if spec["turns"] else []) + \
        (["slide"] if spec.get("slides") else [])
    vacuous = [f"{k} in loop {loop + 1}" for k in kinds for loop in (0, 1)
               if counts[(k, loop)] == 0]
    ok = (runs and not missing and not vacuous and seek["rest"] <= REST_TOL
          and seek["radius"] <= RADIUS_TOL and seek["angle"] <= ANGLE_TOL
          and seek["slide"] <= REST_TOL and seek["phase"] <= REST_TOL
          and seek["upright"] <= UPRIGHT_TOL and free["rest"] <= REST_TOL
          and free["turn"] <= RADIUS_TOL and free["slide"] <= REST_TOL)
    print(f"{name}: clock {r['t0']:.2f} -> {r['t1']:.2f} s and on to "
          f"{(r['free'][-1]['t'] if r['free'] else 0):.2f} s (cycle {spec['cycle']} s); paused, "
          f"both loops: rests {seek['rest']:.2e} px, arcs {seek['radius']:.2e} px and "
          f"{seek['angle']:.2e} deg, slides {seek['slide']:.2e} px, phase {seek['phase']:.2e} px, "
          f"uprights {seek['upright']:.2e} deg; free-running, {len(r['free'])} readings: rests "
          f"{free['rest']:.2e} px, on the circle {free['turn']:.2e} px, on the segment "
          f"{free['slide']:.2e} px"
          + (f"; missing {sorted(set(missing))[:3]}" if missing else "")
          + (f"; no readings of {', '.join(vacuous)}" if vacuous else "")
          + ("" if runs else "; THE CLOCK DID NOT RUN")
          + f" -> {'ok' if ok else 'FAILED'}")
    return ok


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
    failures = sum(0 if check(runner, root, n) else 1 for n in names)
    print(f"webkit: {len(names) - failures} of {len(names)} motions hold")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
