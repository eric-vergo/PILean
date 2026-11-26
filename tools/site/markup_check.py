# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
"""Checks that the figures' markup in a built site has no script, no inline event handler and no
script address: python3 -I markup_check.py SITE_DIR (the html-multi folder).

The pages are parsed as HTML; inside each `figure.pilean-figure`, the figures page's list and
each figure's page (`div.pilean-figure-page`), an
element named `script`, an attribute whose name starts with `on`, or an attribute value that
starts with `javascript:` (ignoring case and white space) is reported. Text, such as a caption
that spells out markup, is not markup and is not reported.

Inside a motion (`div.pilean-motion`, which must carry `data-bp-motion`) nothing may be active at
all: besides the above, no link, form control, frame, embedded object, `foreignObject`, `use` or
`image`; no animation that starts or ends on anything but the clock (`begin` and `end` must be
clock values or `indefinite`), no `restart`; and no tab stop but the stage
(`div.pilean-motion-stage`, `tabindex="0"`).
"""

import glob
import html.parser
import re
import sys

INERT_IN_MOTION = {"a", "button", "input", "select", "textarea", "form", "iframe", "object",
                   "embed", "foreignobject", "use", "image", "area", "audio", "video"}
CLOCK = re.compile(r"^\s*(indefinite|[+-]?[0-9:.]+(h|min|s|ms)?)(\s*;\s*(indefinite|"
                   r"[+-]?[0-9:.]+(h|min|s|ms)?))*\s*$")


class Figures(html.parser.HTMLParser):
    """Collects what is active in figures and counts the figures seen."""

    VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source",
            "track", "wbr"}

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.stack = []
        self.seen = 0
        self.bad = []
        self.motion = None
        self.motions = 0

    @staticmethod
    def starts_part(tag, attrs):
        cls = (dict(attrs).get("class") or "").split()
        return (tag == "figure" and "pilean-figure" in cls) or \
            (tag == "div" and ("pilean-figure-list" in cls or "pilean-figure-page" in cls))

    def handle_starttag(self, tag, attrs):
        if not self.stack:
            if self.starts_part(tag, attrs):
                self.seen += 1
                self.stack = [tag]
            return
        if tag == "script":
            self.bad.append("a script element")
        cls = (dict(attrs).get("class") or "").split()
        if self.motion is None and tag == "div" and "pilean-motion" in cls:
            self.motion = len(self.stack)
            self.motions += 1
            if "data-bp-motion" not in dict(attrs):
                self.bad.append("a motion without data-bp-motion")
        elif self.motion is not None:
            a = {k.lower(): v for k, v in attrs}
            if tag in INERT_IN_MOTION:
                self.bad.append(f"a {tag} element in a motion")
            if tag in ("animate", "animatetransform", "set", "animatemotion"):
                for k in ("begin", "end"):
                    if k in a and not CLOCK.match(a[k] or ""):
                        self.bad.append(f"an animation in a motion whose {k} is {a[k]!r}")
                if "restart" in a:
                    self.bad.append("an animation in a motion with restart")
            if "tabindex" in a and not (tag == "div" and "pilean-motion-stage" in cls and
                                        a["tabindex"] == "0"):
                self.bad.append(f"a tab stop in a motion ({tag})")
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
        if self.motion is not None and len(self.stack) <= self.motion:
            self.motion = None


def main(root: str) -> int:
    seen, bad, motions = 0, [], 0
    for path in sorted(glob.glob(root + "/**/index.html", recursive=True)):
        with open(path, encoding="utf-8") as f:
            p = Figures()
            p.feed(f.read())
        seen += p.seen
        motions += p.motions
        bad += [f"{path}: {b}" for b in p.bad]
    for line in bad:
        print(f"active markup in a figure: {line}")
    if seen < 5:
        print(f"expected the figures and the figures page, found {seen} parts")
        return 1
    print(f"markup: {seen} figures and lists, none active, {motions} motions with nothing active")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
