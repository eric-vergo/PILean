# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
"""Checks that every inline picture of a built site is the body of a file the manifest lists.

    python3 -I inline_check.py SITE_DIR      (the html-multi folder)

Each `svg.pilean-inline-svg` of a page must name its file of the figures folder
(`data-pilean-file`); the file must be listed in `manifest.json` with the SHA-256 of its bytes;
and the page's picture, once what the page adds is taken away (the theme `style` element, the
prefix of its ids, the links around elements that name a declaration, the root's page
attributes), must be the file's picture without its source record (the `title`, `desc` and
`metadata` the build puts first), element for element and attribute for attribute. Exit status
0 when every picture holds, 1 otherwise (each failure is printed).
"""

import glob
import hashlib
import json
import os
import re
import sys
import xml.etree.ElementTree as ET

SVG_NS = "{http://www.w3.org/2000/svg}"
SOURCE_NS = "{https://github.com/eric-vergo/PILean/ns/source/1}"
ROOT_KEEP = ("width", "height", "viewBox")
START = re.compile(r"<svg\b[^>]*\bclass=\"pilean-inline-svg[^\"]*\"[^>]*>")
TAG = re.compile(r"<(/?)svg\b[^>]*?(/?)>")


def inline_svgs(text):
    """The text of each inline picture of a page (nested `svg` elements counted)."""
    out = []
    for m in START.finditer(text):
        depth, pos = 0, m.start()
        for t in TAG.finditer(text, m.start()):
            if t.group(1):
                depth -= 1
            elif not t.group(2):
                depth += 1
            if depth == 0:
                out.append(text[m.start():t.end()])
                pos = t.end()
                break
        if pos == m.start():
            out.append(None)
    return out


def unprefix(value, key, pfx):
    if key == "id":
        return value[len(pfx):] if value.startswith(pfx) else value
    if key == "href" or key.endswith("}href") or key.endswith(":href"):
        return "#" + value[len(pfx) + 1:] if value.startswith("#" + pfx) else value
    return value.replace("url(#" + pfx, "url(#")


def page_children(el, pfx):
    """The children of a page element as the file has them."""
    out = []
    for c in el:
        if c.tag == SVG_NS + "a" and "pilean-decl-link" in (c.get("class") or "").split():
            if len(c) != 1:
                raise ValueError("a declaration link that does not hold one element")
            inner = c[0]
            inner.tail = c.tail
            out.append(normal(inner, pfx))
        else:
            out.append(normal(c, pfx))
    return out


def normal(el, pfx):
    copy = ET.Element(el.tag, {k: unprefix(v, k, pfx) for k, v in el.attrib.items()})
    copy.text, copy.tail = el.text, el.tail
    copy.extend(page_children(el, pfx))
    return copy


def same(a, b, path="svg"):
    """None if the trees agree, else where they differ."""
    if a.tag != b.tag:
        return f"{path}: element {b.tag} in the file, {a.tag} in the page"
    if a.attrib != b.attrib:
        return f"{path}: attributes {b.attrib} in the file, {a.attrib} in the page"
    if (a.text or "").strip() != (b.text or "").strip():
        return f"{path}: text {b.text!r} in the file, {a.text!r} in the page"
    if len(a) != len(b):
        return f"{path}: {len(b)} children in the file, {len(a)} in the page"
    for i, (x, y) in enumerate(zip(a, b)):
        why = same(x, y, f"{path}/{y.tag.replace(SVG_NS, '')}[{i}]")
        if why:
            return why
    return None


def file_body(data):
    root = ET.fromstring(data)
    kids = list(root)
    record = [k.tag for k in kids[:3]]
    if record != [SVG_NS + "title", SVG_NS + "desc", SVG_NS + "metadata"] or \
            kids[2].find(SOURCE_NS + "source") is None:
        raise ValueError("no source record at the start of the file")
    body = ET.Element(root.tag, {k: v for k, v in root.attrib.items() if k in ROOT_KEEP})
    body.extend(kids[3:])
    return body


def page_body(text):
    root = ET.fromstring(text)
    pfx = (root.get("id") or "") + "-"
    kids = list(root)
    if kids and kids[0].tag == SVG_NS + "style" and kids[0].get("class") == "pilean-theme":
        kids = kids[1:]
    body = ET.Element(root.tag, {k: v for k, v in root.attrib.items() if k in ROOT_KEEP})
    holder = ET.Element("x")
    holder.extend(kids)
    body.extend(page_children(holder, pfx))
    return body


def main(site):
    figs = os.path.join(site, "-verso-data", "pilean-figures")
    with open(os.path.join(figs, "manifest.json"), encoding="utf-8") as f:
        manifest = {e["path"]: e for e in json.load(f)["files"]}
    checked, failures = 0, []
    for page in sorted(glob.glob(os.path.join(site, "**", "index.html"), recursive=True)):
        with open(page, encoding="utf-8") as f:
            text = f.read()
        rel = os.path.relpath(page, site)
        for svg in inline_svgs(text):
            checked += 1
            if svg is None:
                failures.append(f"{rel}: an inline picture is not closed")
                continue
            m = re.search(r'data-pilean-file="([^"]*)"', svg.split(">", 1)[0])
            pid = re.search(r'\bid="([^"]*)"', svg.split(">", 1)[0])
            name = f"{rel} #{pid.group(1) if pid else '?'}"
            if not m:
                failures.append(f"{name}: names no file")
                continue
            path = m.group(1)
            entry = manifest.get(path)
            if entry is None or ".." in path.split("/"):
                failures.append(f"{name}: {path} is not in the manifest")
                continue
            with open(os.path.join(figs, path), "rb") as f:
                data = f.read()
            if hashlib.sha256(data).hexdigest() != entry["sha256"]:
                failures.append(f"{name}: {path} does not have the manifest's SHA-256")
                continue
            try:
                why = same(page_body(svg), file_body(data))
            except (ET.ParseError, ValueError) as e:
                why = f"cannot be read ({e})"
            if why:
                failures.append(f"{name}: differs from {path}: {why}")
    for line in failures:
        print(f"inline: {line}")
    print(f"inline: {checked - len(failures)} of {checked} inline pictures match their files")
    return 1 if failures or checked == 0 else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
