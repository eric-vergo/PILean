# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
"""Checks that every inline picture of a built site is the body of a file the manifest lists.

    python3 -I tools/site/inline_check.py SITE_DIR [--figures DIR]

SITE_DIR is the generator's `html-multi` folder; the figures folder is
`SITE_DIR/-verso-data/pilean-figures` unless `--figures` names another, with its `manifest.json`.
It is one of PILean's site checks (`tools/site/`), which any site built with the Verso adapters
can run.

Each `svg.pilean-inline-svg` of a page must name its file of the figures folder
(`data-pilean-file`); the file must be listed in `manifest.json` with the SHA-256 of its bytes;
the page's theme `style` element must be, character for character, the rules the adapter derives
from the dark colours and tint opacities the manifest records for that file and from the
picture's id (none when the manifest records none); and the page's picture, once what the page
adds is taken away (that `style` element, the prefix of its ids, the links around elements that
name a declaration, the root's page attributes), must be the file's picture without its source
record (the `title`, `desc` and `metadata` the build puts first), element for element and
attribute for attribute. Other CSS of the page is not checked.

A motion's moving picture (the manifest's entry has `kind` `motion`) is checked against its
animated SVG file as `docs/TRUST.md` asks ("What a page that shows a motion must do"): the file's
own `title` and `desc` (when it has them) are skipped, then its source record; its `style` element
must be, character for character, the fixed reduced-motion rule (`Animation.reducedMotionStyle`);
its last element must be the poster group, which must be, element for element, the still of the
poster key the page names (`data-pilean-poster`; the file `-key-k.svg` beside the animated SVG, of
the same rendition, listed in the manifest with its SHA-256) with every id prefixed `poster-`
(after the background and the titles the file draws before its moving picture, which a picture of
panels does not repeat in it); and the page's picture must be the file's nodes between that
`style` element and the poster group, element for element, once what the page adds is taken away
(its prefix is also on every `data-pilean-actor`). The manifest must record the motion as checked
strictly: `checks` `fail` and `errorsLeft` 0. The pictures shown with a motion are its files'
too: the still over the moving picture (`span.pilean-motion-still`) is exactly the poster key's
still (`-key-k.svg` for the poster `k` the page names, with `-key-k-dark.svg` when the manifest
lists it, and the narrow rendition's `-narrow-key-k.svg` and its dark twin as the sources for
small screens when the motion has one), and the list of stills (`ol.pilean-motion-keys`, left out
only on the figure's page, `pilean-motion-bare`) has one item for each key `k`, in order, showing
exactly the files of key `k` likewise, with its caption `Step k+1 of N: …`.

Exit status 0 when every picture holds, 1 otherwise (each failure is printed).
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
# `Animation.reducedMotionStyle` (PILean/Anim/Animation.lean), the text of every motion file's
# `style` element.
REDUCED_MOTION = (".pilean-motion-poster{display:none}@media (prefers-reduced-motion: reduce)"
                  "{.pilean-motion-poster{display:inline}.pilean-motion-live"
                  "{visibility:hidden;opacity:0}}")
START = re.compile(r"<svg\b[^>]*\bclass=\"pilean-inline-svg[^\"]*\"[^>]*>")
TAG = re.compile(r"<(/?)svg\b[^>]*?(/?)>")


def inline_svgs(text):
    """The text of each inline picture of a page (nested `svg` elements counted), with the
    position where it ends."""
    out = []
    for m in START.finditer(text):
        depth, pos = 0, m.start()
        for t in TAG.finditer(text, m.start()):
            if t.group(1):
                depth -= 1
            elif not t.group(2):
                depth += 1
            if depth == 0:
                out.append((text[m.start():t.end()], t.end()))
                pos = t.end()
                break
        if pos == m.start():
            out.append((None, m.start()))
    return out


def unprefix(value, key, pfx):
    if key in ("id", "data-pilean-actor"):
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


def after_record(kids, own_head=False):
    """The children after the source record (`title`, `desc`, `metadata` with the record), which
    comes first, or, with `own_head`, after the file's own `title` and `desc` when it has them."""
    for start in ([0, 1, 2] if own_head else [0]):
        record = [k.tag for k in kids[start:start + 3]]
        own = [k.tag for k in kids[:start]]
        if own not in ([], [SVG_NS + "title"], [SVG_NS + "desc"],
                       [SVG_NS + "title", SVG_NS + "desc"]):
            continue
        if record == [SVG_NS + "title", SVG_NS + "desc", SVG_NS + "metadata"] and \
                kids[start + 2].find(SOURCE_NS + "source") is not None:
            return kids[start + 3:]
    raise ValueError("no source record at the start of the file")


def body_of(root, kids):
    body = ET.Element(root.tag, {k: v for k, v in root.attrib.items() if k in ROOT_KEEP})
    body.extend(kids)
    return body


def file_body(data):
    root = ET.fromstring(data)
    return body_of(root, after_record(list(root)))


def motion_parts(data):
    """The parts of a motion's animated SVG: the nodes the page shows (between the
    reduced-motion `style` element and the poster group), those of them before the moving
    picture's group, and the poster group; an error if the file is not made so."""
    root = ET.fromstring(data)
    kids = after_record(list(root), own_head=True)
    if not kids or kids[0].tag != SVG_NS + "style":
        raise ValueError("no reduced-motion style element after the source record")
    if (kids[0].text or "") != REDUCED_MOTION or len(kids[0]):
        raise ValueError("its style element is not the fixed reduced-motion rule")
    last = kids[-1]
    if last.tag != SVG_NS + "g" or last.get("class") != "pilean-motion-poster":
        raise ValueError("its last element is not the poster group")
    live = kids[1:-1]
    lead = []
    for k in live:
        if k.tag == SVG_NS + "g" and k.get("class") == "pilean-motion-live":
            break
        lead.append(k)
    else:
        raise ValueError("no moving picture (a group of class pilean-motion-live)")
    if sum(1 for _ in root.iter(SVG_NS + "style")) != 1:
        raise ValueError("a style element besides the reduced-motion rule")
    return body_of(root, live), lead, last


def poster_problem(poster, lead, still):
    """None if the poster group is the poster key's still with the prefix `poster-` on every id
    (after the nodes `lead` the file draws before its moving picture, when the still has them),
    else why not."""
    ids = [e.get("id") for e in poster.iter() if e.get("id") is not None]
    if any(not i.startswith("poster-") for i in ids):
        return "an id of the poster group lacks the prefix poster-"
    holder = ET.Element("x")
    holder.extend(normal(c, "poster-") for c in poster)
    shown = list(holder)
    kids = list(still)
    if len(kids) < len(shown):
        return f"the poster group has {len(shown)} elements, the still {len(kids)}"
    head, tail = kids[:len(kids) - len(shown)], kids[len(kids) - len(shown):]
    if head:
        why = same(body_of(still, lead), body_of(still, head), "still")
        if why:
            return f"the still does not start with what the file draws first: {why}"
    return same(body_of(still, shown), body_of(still, tail), "poster")


def dom_safe(s):
    """The id as the adapter writes it (`domSafe`): ASCII letters, digits, `-` and `_` kept."""
    return "".join(c if (c.isascii() and c.isalnum()) or c in "-_" else "_" for c in s)


def theme_css(pid, pairs, opacities):
    """The theme rules the adapter writes for a picture (`themeCss`), empty without any."""
    if not pairs and not opacities:
        return ""
    pid = dom_safe(pid)
    sel = f"#{pid}" if pid[:1].isalpha() else f'svg[id="{pid}"]'

    def rules(pre):
        out = "".join(f'{pre} {sel} [fill="{a}"]{{fill:{b}}}'
                      f'{pre} {sel} [stroke="{a}"]{{stroke:{b}}}' for a, b in pairs)
        return out + "".join(f'{pre} {sel} [fill-opacity="{a}"]{{fill-opacity:{b}}}'
                             for a, b in opacities)
    return (rules('html[data-theme="dark"]') + "@media (prefers-color-scheme: dark){" +
            rules('html:not([data-theme="light"])') + "}")


def page_theme(text):
    """The text of the picture's theme `style` element, empty without one; an error if the
    picture has another `style` element."""
    root = ET.fromstring(text)
    styles = [k for k in root.iter(SVG_NS + "style")]
    kids = list(root)
    first = kids[0] if kids and kids[0].tag == SVG_NS + "style" and \
        kids[0].get("class") == "pilean-theme" else None
    if any(st is not first for st in styles):
        raise ValueError("a style element other than the theme's first one")
    return root.get("id") or "", (first.text or "") if first is not None else ""


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


def still_path(path, poster):
    """The file of key `poster`'s still beside the animated SVG `path` of a rendition."""
    return f"{path[:-len('.svg')]}-key-{poster}.svg"


def motion_problem(svg, data, figs, path, entry, manifest):
    """None if the page's moving picture `svg` is the motion file's, as the module says."""
    if entry.get("checks") != "fail" or entry.get("errorsLeft") != 0:
        return (f"the manifest records the motion at the check level {entry.get('checks')} "
                f"with {entry.get('errorsLeft')} errors left, not checked strictly")
    root = ET.fromstring(svg)
    poster = root.get("data-pilean-poster")
    if poster is None or not poster.isdigit():
        return "the page names no poster key (data-pilean-poster)"
    live, lead, group = motion_parts(data)
    spath = still_path(path, poster)
    sentry = manifest.get(spath)
    if sentry is None:
        return f"the poster key's still {spath} is not in the manifest"
    with open(os.path.join(figs, spath), "rb") as f:
        sdata = f.read()
    if hashlib.sha256(sdata).hexdigest() != sentry["sha256"]:
        return f"{spath} does not have the manifest's SHA-256"
    why = poster_problem(group, lead, file_body(sdata))
    if why:
        return f"its poster group is not {spath}: {why}"
    return same(page_body(svg), live)


KEYS = re.compile(r'</div><ol class="pilean-motion-keys"[^>]*>(.*?)</ol>', re.S)
WRAPPER = re.compile(r'<div class="(pilean-motion(?: [^"]*)?)" data-bp-motion')


def refs(html, attr):
    """The paths below the figures folder that the attribute `attr` of the markup `html` names."""
    return sorted(re.findall(attr + r'="[^"]*?pilean-figures/([^"]+)"', html))


def key_files(stem, k, manifest, narrow):
    """The files a page shows for key `k` of the motion whose animated SVG is `stem.svg`: the
    `src`s (the light still and its dark twin, if listed) and the `srcset`s (the narrow
    rendition's, if it has one)."""
    def pair(s):
        return [p for p in (f"{s}-key-{k}.svg", f"{s}-key-{k}-dark.svg") if p in manifest]
    return sorted(pair(stem)), sorted(pair(stem + "-narrow") if narrow else [])


def stills_problem(text, end, path, manifest, entry, poster):
    """None if the pictures shown with the moving picture that ends at `end` are the motion's
    files, as the module docstring says, else why not."""
    stem = path[:-len(".svg")]
    narrow = f"{stem}-narrow.svg" in manifest
    m = re.compile(r'<span class="pilean-motion-still"[^>]*>(.*?)</span>', re.S).search(text, end)
    if m is None:
        return "no poster still over the moving picture"
    want = key_files(stem, poster, manifest, narrow)
    have = (refs(m.group(1), "src"), refs(m.group(1), "srcset"))
    if have != want:
        return f"the still over it shows {have}, not the poster key's files {want}"
    rest = text[m.end():m.end() + 200]
    if rest.startswith('</div></div>'):
        wrappers = list(WRAPPER.finditer(text, 0, end))
        bare = bool(wrappers) and "pilean-motion-bare" in wrappers[-1].group(1).split()
        return None if bare else "no list of stills, and not marked pilean-motion-bare"
    lm = KEYS.match(text, m.end())
    if lm is None:
        return "no list of stills after the stage"
    items = re.findall(r'<li class="pilean-motion-key"[^>]*>(.*?)</li>', lm.group(1), re.S)
    n = entry.get("keys")
    if len(items) != n:
        return f"{len(items)} stills listed for {n} keys"
    for k, li in enumerate(items):
        want = key_files(stem, k, manifest, narrow)
        have = (refs(li, "src"), refs(li, "srcset"))
        if have != want:
            return f"still {k} shows {have}, not {want}"
        if f"Step {k + 1} of {n}: " not in li:
            return f"still {k} has no caption Step {k + 1} of {n}"
    return None


def main(site, figs=None):
    figs = figs or os.path.join(site, "-verso-data", "pilean-figures")
    with open(os.path.join(figs, "manifest.json"), encoding="utf-8") as f:
        manifest = {e["path"]: e for e in json.load(f)["files"]}
    checked, failures, motions = 0, [], 0
    for page in sorted(glob.glob(os.path.join(site, "**", "index.html"), recursive=True)):
        with open(page, encoding="utf-8") as f:
            text = f.read()
        rel = os.path.relpath(page, site)
        for svg, end in inline_svgs(text):
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
                pid_text, css = page_theme(svg)
                want = theme_css(pid_text, entry.get("darkColours", []),
                                 entry.get("darkOpacities", []))
                if css != want:
                    why = "its theme rules are not those the manifest records"
                elif entry.get("kind") == "motion":
                    motions += 1
                    why = motion_problem(svg, data, figs, path, entry, manifest)
                    poster = ET.fromstring(svg).get("data-pilean-poster") or ""
                    if not why and "pilean-motion-wide" in (ET.fromstring(svg).get("class") or ""):
                        why = stills_problem(text, end, path, manifest, entry, int(poster))
                else:
                    why = same(page_body(svg), file_body(data))
            except (ET.ParseError, ValueError) as e:
                why = f"cannot be read ({e})"
            if why:
                failures.append(f"{name}: differs from {path}: {why}")
    for line in failures:
        print(f"inline: {line}")
    print(f"inline: {checked - len(failures)} of {checked} inline pictures match their files "
          f"({motions} of them moving pictures of motions)")
    return 1 if failures or checked == 0 else 0


if __name__ == "__main__":
    args = sys.argv[1:]
    if len(args) not in (1, 3) or (len(args) == 3 and args[1] != "--figures"):
        print("usage: inline_check.py SITE_DIR [--figures DIR]")
        sys.exit(2)
    sys.exit(main(args[0], args[2] if len(args) == 3 else None))
