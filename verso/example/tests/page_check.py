# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
"""Checks the figures' pages of a built site against its figures folder's manifest:
python3 -I page_check.py SITE_DIR (the html-multi folder).

Every figure the manifest lists (by its declaration) must have exactly one page below `Figures/`
(an element with `data-pilean-page`), and each page must agree with the manifest:

* the files it offers for download are the figure's files, with the manifest's size and SHA-256;
* the standing it states (`data-pilean-standing`, `data-pilean-theorems`) is the standing every
  file of the figure records in the manifest (`standing`, `proves`);
* its words follow the standing: "Tied to its object by the theorem" and a section with each
  theorem's statement for a proved figure, "Illustration: not tied to a Lean object by a theorem"
  and no "Tied to its object" for an illustration;
* every verdict of `pilean-verify` it shows is `ok`.

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

    def handle_data(self, data):
        self.text.append(data)


def main(site):
    problems = []
    figs = os.path.join(site, "-verso-data", "pilean-figures")
    with open(os.path.join(figs, "manifest.json"), encoding="utf-8") as f:
        files = json.load(f)["files"]
    by_decl = {}
    for e in files:
        by_decl.setdefault(e["decl"], []).append(e)
    seen = {}
    for path in sorted(glob.glob(os.path.join(site, "Figures", "*", "index.html"))):
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
            if e.get("standing") != standing or (e.get("proves") or "") != theorems:
                problems.append(f"{where}: states {standing} {theorems!r}, {e['path']} records "
                                f"{e.get('standing')} {e.get('proves')!r}")
        text = " ".join(" ".join(p.text).split())
        tied = "Tied to its object by the theorem" in text
        if standing == "proved":
            if not tied:
                problems.append(f"{where}: proved, but does not say it is tied to its object")
            if " ".join(p.decls) != theorems:
                problems.append(f"{where}: the statements shown are of {p.decls}, not {theorems!r}")
        else:
            if p.decls:
                problems.append(f"{where}: an illustration with theorem statements")
            if tied or "Tied to its object" in text:
                problems.append(f"{where}: an illustration that says it is tied to its object")
            if "Illustration: not tied to a Lean object by a theorem" not in text:
                problems.append(f"{where}: an illustration that does not say so")
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
    sys.exit(main(sys.argv[1]))
