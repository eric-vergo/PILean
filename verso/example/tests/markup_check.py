# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
"""Checks that the figures' markup in a built site has no script, no inline event handler and no
script address: python3 -I markup_check.py SITE_DIR (the html-multi folder).

The pages are parsed as HTML; inside each `figure.pilean-figure` and the figures page's list, an
element named `script`, an attribute whose name starts with `on`, or an attribute value that
starts with `javascript:` (ignoring case and white space) is reported. Text, such as a caption
that spells out markup, is not markup and is not reported.
"""

import glob
import html.parser
import sys


class Figures(html.parser.HTMLParser):
    """Collects what is active in figures and counts the figures seen."""

    VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source",
            "track", "wbr"}

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.stack = []
        self.seen = 0
        self.bad = []

    @staticmethod
    def starts_part(tag, attrs):
        cls = (dict(attrs).get("class") or "").split()
        return (tag == "figure" and "pilean-figure" in cls) or \
            (tag == "div" and "pilean-figure-list" in cls)

    def handle_starttag(self, tag, attrs):
        if not self.stack:
            if self.starts_part(tag, attrs):
                self.seen += 1
                self.stack = [tag]
            return
        if tag == "script":
            self.bad.append("a script element")
        for k, v in attrs:
            if k.lower().startswith("on"):
                self.bad.append(f"the attribute {k}")
            if v and "".join(v.split()).lower().startswith("javascript:"):
                self.bad.append(f"a script address in {k}")
        if tag not in self.VOID:
            self.stack.append(tag)

    def handle_startendtag(self, tag, attrs):
        inside = bool(self.stack)
        self.handle_starttag(tag, attrs)
        if inside and tag not in self.VOID and self.stack and self.stack[-1] == tag:
            self.stack.pop()

    def handle_endtag(self, tag):
        if tag not in self.stack:
            return
        while self.stack and self.stack.pop() != tag:
            pass


def main(root: str) -> int:
    seen, bad = 0, []
    for path in sorted(glob.glob(root + "/**/index.html", recursive=True)):
        with open(path, encoding="utf-8") as f:
            p = Figures()
            p.feed(f.read())
        seen += p.seen
        bad += [f"{path}: {b}" for b in p.bad]
    for line in bad:
        print(f"active markup in a figure: {line}")
    if seen < 5:
        print(f"expected the figures and the figures page, found {seen} parts")
        return 1
    print(f"markup: {seen} figures and lists, none active")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
