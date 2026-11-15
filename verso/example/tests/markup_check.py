# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
"""Checks that the figures' markup in a built site has no script, no inline event handler and no
script address: python3 -I markup_check.py SITE_DIR (the html-multi folder)."""

import glob
import re
import sys

FIGURE = re.compile(r'<figure[^>]*class="pilean-figure.*?</figure>', re.S)
LIST = re.compile(r'<div class="pilean-figure-list">.*?</ol>\s*</div>', re.S)
ACTIVE = re.compile(r'<script|\son[a-z]+\s*=|javascript:', re.I)


def main(root: str) -> int:
    seen, bad = 0, []
    for path in sorted(glob.glob(root + "/**/index.html", recursive=True)):
        with open(path, encoding="utf-8") as f:
            text = f.read()
        parts = FIGURE.findall(text) + LIST.findall(text)
        seen += len(parts)
        bad += [path for part in parts if ACTIVE.search(part)]
    for path in bad:
        print(f"active markup in a figure: {path}")
    if seen < 5:
        print(f"expected the four figures and the figures page, found {seen} parts")
        return 1
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
