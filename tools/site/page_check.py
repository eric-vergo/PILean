# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
"""Checks the figures' pages of a built site against its figures folder's manifest:

    python3 -I tools/site/page_check.py SITE_DIR [--figures DIR]

SITE_DIR is the generator's `html-multi` folder; the figures folder is
`SITE_DIR/-verso-data/pilean-figures` unless `--figures` names another. It is one of PILean's
site checks (`tools/site/`).

Every figure the manifest lists (by its declaration) must have exactly one page in the site (an
element with `data-pilean-page`), and each page must agree with the manifest:

* the files it offers for download are the figure's files, with the manifest's size and SHA-256;
* the standing it states (`data-pilean-standing`, `data-pilean-theorems`) is the standing every
  file of the figure records in the manifest (`standing`, `theorems`);
* its words follow the standing: "Linked theorem" and a section with each theorem's statement
  for a linked figure, each followed by "PILean checked that T is proved from the standard axioms
  and that its statement names this figure; it did not check what T says.";
  "Illustration: no theorem is linked to it" and no "Linked theorem" for an illustration; and no
  page says "Tied to its object" or "proved by";
* every verdict of `pilean-verify` it shows is `ok`;
* for a motion (its files record `kind` `motion`): the motion's sentence, "An animation drawn
  from N key frames; the stills are the key figures as drawn.", with N the manifest's `keys` (and
  ", S of them shown as stills" after "key frames" when the manifest lists the S keys that are
  stills, `stills`), followed by what the browser does between key frames; for a motion not
  checked strictly, what that means ("It was built at the check level …"); for a linked motion,
  what a theorem about a motion can state; the table of the steps (`table.pilean-motion-steps`)
  with one row for each of the N - 1 steps (besides the rows of rests, `tr.pilean-motion-rest`);
  and the S stills with their captions ("Step k of S: …", S = N when every key is a still); and
  its files are exactly those the adapters write for a motion (`motion_files`).

It prints one line per problem and exits 1 if there is any, 0 otherwise.
"""

import glob
import html.parser
import json
import os
import sys


class Page(html.parser.HTMLParser):
    """Collects the page root's attributes, the downloads, verdicts, theorem sections and text."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.root = None
        self.downloads = []
        self.verdicts = []
        self.decls = []
        self.text = []
        self.steps = None
        self.in_body = False
        self.keys = 0

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        cls = (a.get("class") or "").split()
        if "data-pilean-page" in a:
            if self.root is None:
                self.root = a
            else:
                self.root["twice"] = "yes"
        if tag == "a" and "pilean-page-download" in cls:
            self.downloads.append(a)
        if "pilean-page-verdict" in cls:
            self.verdicts.append(a.get("data-verdict"))
        if tag == "section" and "pilean-page-theorem" in cls:
            self.decls.append(a.get("data-lean-decl"))
        if tag == "table" and "pilean-motion-steps" in cls:
            self.steps = 0
        if tag == "tbody" and self.steps is not None:
            self.in_body = True
        if tag == "tr" and self.in_body and "pilean-motion-rest" not in cls:
            self.steps += 1
        if tag == "li" and "pilean-page-motion-key" in cls:
            self.keys += 1

    def handle_endtag(self, tag):
        if tag == "tbody":
            self.in_body = False

    def handle_data(self, data):
        self.text.append(data)


def motion_files(stem, keys, narrow, dark, rasters=False):
    """The files the Verso adapters write for a motion whose animated SVG is `stem.svg`, whose
    stills are the keys `keys` (a number `n`: the keys `0` to `n - 1`, every key a still; or the
    list of the keys that are stills, `stills` in the manifest), with a narrow rendition or not, a
    dark twin or not, and the APNG and GIF of its baked frames or not (`MotionFigure.rasters`):
    the animated SVG, the poster's PNG and PDF, the contact sheet's SVG, PNG and PDF, the SVG and
    PNG of each still (`-key-k`, `k` its key); with a narrow rendition its animated SVG and the
    SVG and PNG of each of its stills; with a dark twin the SVG of each still at each width
    (`-key-k-dark.svg`), all a page shows of the dark motion. So `7 + 6 s` files for `s` stills
    with a narrow rendition and a dark twin, `6 + 3 s` with a dark twin only, `7 + 4 s` and
    `6 + 2 s` without one."""
    keys = list(range(keys)) if isinstance(keys, int) else list(keys)
    out = [f"{stem}.svg", f"{stem}-poster.png", f"{stem}-poster.pdf", f"{stem}-keys.svg",
           f"{stem}-keys.png", f"{stem}-keys.pdf"]
    stems = [stem] + ([stem + "-narrow"] if narrow else [])
    if narrow:
        out.append(f"{stem}-narrow.svg")
    for s in stems:
        for k in keys:
            out += [f"{s}-key-{k}.svg", f"{s}-key-{k}.png"] + \
                ([f"{s}-key-{k}-dark.svg"] if dark else [])
    if rasters:
        out += [f"{stem}.png", f"{stem}.gif"]
    return sorted(out)


def main(site, figs=None):
    problems = []
    figs = figs or os.path.join(site, "-verso-data", "pilean-figures")
    with open(os.path.join(figs, "manifest.json"), encoding="utf-8") as f:
        files = json.load(f)["files"]
    by_decl = {}
    for e in files:
        by_decl.setdefault(e["decl"], []).append(e)
    seen = {}
    for path in sorted(glob.glob(os.path.join(site, "**", "index.html"), recursive=True)):
        p = Page()
        with open(path, encoding="utf-8") as f:
            p.feed(f.read())
        if p.root is None:
            continue
        decl = p.root["data-pilean-page"]
        where = os.path.relpath(path, site)
        if "twice" in p.root:
            problems.append(f"{where}: more than one page root")
        if decl in seen:
            problems.append(f"{where}: a second page for {decl} ({seen[decl]})")
        seen[decl] = where
        entries = by_decl.get(decl, [])
        if not entries:
            problems.append(f"{where}: {decl} has no file in the manifest")
            continue
        prefix = "-verso-data/pilean-figures/"
        offered = {d.get("href", "").split(prefix, 1)[-1]: d for d in p.downloads}
        for e in entries:
            d = offered.pop(e["path"], None)
            if d is None:
                problems.append(f"{where}: does not offer {e['path']}")
            elif d.get("data-sha256") != e["sha256"] or d.get("data-bytes") != str(e["bytes"]):
                problems.append(f"{where}: {e['path']} has another size or SHA-256 than listed")
        for extra in offered:
            problems.append(f"{where}: offers {extra}, which is not the figure's file")
        standing = p.root.get("data-pilean-standing")
        theorems = p.root.get("data-pilean-theorems") or ""
        for e in entries:
            # the manifest lists the theorems as an array; the page's attribute joins them with
            # single spaces
            if e.get("standing") != standing or " ".join(e.get("theorems") or []) != theorems:
                problems.append(f"{where}: states {standing} {theorems!r}, {e['path']} records "
                                f"{e.get('standing')} {e.get('theorems')!r}")
        text = " ".join(" ".join(p.text).split())
        linked = "Linked theorem" in text
        if "Tied to its object" in text or "proved by" in text.lower():
            problems.append(f"{where}: says that the figure is tied to its object or proved")
        if standing == "linked":
            if not linked:
                problems.append(f"{where}: linked, but does not say so")
            if " ".join(p.decls) != theorems:
                problems.append(f"{where}: the statements shown are of {p.decls}, not {theorems!r}")
            # the statements shown, by name (a name in guillemets may hold a space)
            for t in p.decls:
                said = (f"PILean checked that {t} is proved from the standard axioms and that its "
                        f"statement names this figure; it did not check what {t} says.")
                if said not in text:
                    problems.append(f"{where}: does not say what PILean checked of {t}")
        else:
            if p.decls:
                problems.append(f"{where}: an illustration with theorem statements")
            if linked:
                problems.append(f"{where}: an illustration that names a linked theorem")
            if "Illustration: no theorem is linked to it" not in text:
                problems.append(f"{where}: an illustration that does not say so")
        motion = entries[0].get("kind") == "motion"
        if motion:
            n = entries[0].get("keys")
            stills = entries[0].get("stills")
            shown = len(stills) if stills is not None else n
            paths = sorted(e["path"] for e in entries)
            stem = min((p for p in paths if p.endswith(".svg")), key=len)[:-len(".svg")]
            want = motion_files(stem, stills if stills is not None else n, entries[0].get("narrow"),
                                any(p.endswith("-dark.svg") for p in paths),
                                f"{stem}.gif" in paths)
            if paths != want:
                missing = sorted(set(want) - set(paths))[:6]
                extra = sorted(set(paths) - set(want))[:6]
                what = f"missing {missing}, extra {extra}" if missing or extra else \
                    "a file listed twice"
                problems.append(f"{where}: the motion's files are not those the adapters write: "
                                f"{what}")
            frames = "key frame" if n == 1 else "key frames"
            if stills is not None:
                frames += (", 1 of them shown as a still" if shown == 1 else
                           f", {shown} of them shown as stills")
            said = (f"An animation drawn from {n} {frames}; the stills are the key figures as "
                    "drawn.")
            if said not in text:
                problems.append(f"{where}: a motion without its sentence ({said!r})")
            elif not ("Between key frames the browser" in text or
                      "Nothing moves between the key frames." in text):
                problems.append(f"{where}: a motion that does not say what the browser draws")
            strict = entries[0].get("checks") == "fail" and entries[0].get("errorsLeft") == 0
            if not strict and "It was built at the check level" not in text:
                problems.append(f"{where}: a motion not checked strictly that does not say so")
            if standing == "linked" and "A theorem about a motion can state its key figures" \
                    not in text:
                problems.append(f"{where}: a linked motion without what its theorem can state")
            if p.steps != n - 1:
                problems.append(f"{where}: a motion of {n} keys with {p.steps} rows of steps")
            if p.keys != shown or \
                    any(f"Step {k} of {shown}:" not in text for k in range(1, shown + 1)):
                problems.append(f"{where}: a motion of {shown} stills with {p.keys} captioned "
                                "stills")
        elif p.steps is not None or "An animation drawn from" in text:
            problems.append(f"{where}: motion words on the page of a figure that is no motion")
        for v in p.verdicts:
            if v != "ok":
                problems.append(f"{where}: shows the verdict {v}")
        if len(p.verdicts) != len(entries):
            problems.append(f"{where}: {len(p.verdicts)} verdicts for {len(entries)} files")
    for decl in by_decl:
        if decl not in seen:
            problems.append(f"{decl}: no page")
    for line in problems:
        print(line)
    return 1 if problems else 0


if __name__ == "__main__":
    args = sys.argv[1:]
    if len(args) not in (1, 3) or (len(args) == 3 and args[1] != "--figures"):
        print("usage: page_check.py SITE_DIR [--figures DIR]")
        sys.exit(2)
    sys.exit(main(args[0], args[2] if len(args) == 3 else None))
