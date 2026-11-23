# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
"""Checks the example site's figures in a headless Chromium (Playwright).

    python3 browser_check.py SITE [SHOTS] [--site-links DIR] [--no-links DIR] [--side-by-side DIR]

SITE is the generator's `html-multi` folder, built with `--figure-repo` and the default link mode
(`ideil`); SHOTS, if given, is a folder for screenshots. The other folders are the same site
built with `--figure-lean-links site`, with `--figure-lean-links none`, and with
`--side-by-side --figure-lean-links site`; the checks of a folder not given are skipped.

Each site is served on 127.0.0.1 with a strict content policy: scripts only from the site's files
and the inline scripts of the head (by hash), no inline event handlers, no plug-ins, nothing from
elsewhere. Checked: every picture loads in the light and the dark theme and the right one is
shown; the source line's links; the figures page; the still frame under reduced motion; no
horizontal scrolling at narrow widths; no content-policy report about a figure. For the
explorers: the slider and the stepper change the frame (by pointer and by keyboard) and say what
they show from the frames' data, whatever the captions hold; one status region speaks, only
when asked; the page scrolls under a wheel or a one-finger swipe, the picture zooms under Ctrl
and the wheel or two fingers; frames of different sizes keep their own view; the script set up
twice acts once; the controls are large enough to touch; an inline element carries its title and
its link; the inline tint follows the theme, also for an id that starts with a digit, and under
a policy that allows the pictures' style elements by hash only; without script every frame is a
grid cell in order and nothing is focusable; reduced motion has no play button; at 360 px the
narrow rendition is shown. The three link modes: `lean:` links, links into the site that a click
follows to an existing anchor (also in the side-by-side layout), and no links. Everything a
figure shows is centred in its container and stays within it: wide, in the narrow column of the
side-by-side layout, and at 360 px, also with a word of 240 letters in a caption and in the
figures page's list. Hostile captions, names and ids show as text and run nothing.
"""

import base64
import functools
import hashlib
import http.server
import re
import sys
import threading

from playwright.sync_api import sync_playwright

HEAD_SCRIPT = re.compile(rb"<script>(.*?)</script>", re.S)
STYLE_ELEMENT = re.compile(rb"<style\b[^>]*>(.*?)</style>", re.S)


def b64sha(data: bytes) -> str:
    return "'sha256-" + base64.b64encode(hashlib.sha256(data).digest()).decode() + "'"


def policy(page: bytes, styles: str) -> str:
    head = page.split(b"</head>", 1)[0]
    hashes = [b64sha(m) for m in HEAD_SCRIPT.findall(head)]
    scripts = " ".join(["'self'", "'wasm-unsafe-eval'"] + hashes)
    if styles == "hashes":
        style = "style-src 'self' " + " ".join(b64sha(m) for m in STYLE_ELEMENT.findall(page)) + \
            "; style-src-attr 'unsafe-inline'"
    else:
        style = "style-src 'self' 'unsafe-inline'"
    return (
        f"default-src 'self'; script-src {scripts}; script-src-attr 'none'; {style}; "
        "object-src 'none'; base-uri 'self'; form-action 'none'; frame-src 'none'; "
        "frame-ancestors 'none'"
    )


class Handler(http.server.SimpleHTTPRequestHandler):
    styles = "inline"

    def log_message(self, *args):
        pass

    def end_headers(self):
        path = self.translate_path(self.path)
        if path.endswith("/"):
            path += "index.html"
        if path.endswith(".html"):
            try:
                with open(path, "rb") as f:
                    self.send_header("Content-Security-Policy", policy(f.read(), self.styles))
            except OSError:
                pass
        super().end_headers()


def serve(site, styles="inline"):
    handler = functools.partial(type("H", (Handler,), {"styles": styles}), directory=site)
    server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), handler)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    return server, f"http://127.0.0.1:{server.server_address[1]}/"


# Verso's release loads its docstring Markdown renderer from jsDelivr, which the policy blocks:
# a report about Verso's page, not about a figure.
VERSO_CDN = "https://cdn.jsdelivr.net/npm/marked@"


def figure_reports(page):
    """The page's content-policy reports, without the one of Verso's own script address and
    those of inline event handlers outside figures (Verso's table of contents has one)."""
    return [r for r in page.evaluate("window.__cspReports")
            if not (r["directive"] == "script-src-attr" and not r["inFigure"])
            and not (r["blocked"] or "").startswith(VERSO_CDN)]


REPORTS = """
window.__liveChanges = [];
document.addEventListener('readystatechange', () => {
  if (document.readyState !== 'interactive') return;
  new MutationObserver(ms => { for (const m of ms) {
    const el = m.target.nodeType === 1 ? m.target : m.target.parentElement;
    const live = el && el.closest('[aria-live], [role=status], [role=alert], output');
    if (live && live.getAttribute('aria-live') !== 'off')
      window.__liveChanges.push(live.className || live.tagName);
  } }).observe(document, {subtree: true, childList: true, characterData: true});
});
window.__cspReports = [];
window.__alerts = [];
window.alert = (m) => window.__alerts.push(String(m));
document.addEventListener('securitypolicyviolation', e => {
  const t = e.target && e.target.closest ? e.target : null;
  window.__cspReports.push({directive: e.effectiveDirective, blocked: e.blockedURI,
    sample: e.sample, source: e.sourceFile,
    inFigure: !!(t && t.closest('.pilean-figure, .pilean-figure-list'))});
});
"""

PAGES = ["Pictures-with-proofs/A-function/", "Pictures-with-proofs/Data/",
         "Pictures-with-proofs/A-relation/", "Pictures-with-proofs/Motion/", "Figures/",
         "Pictures-with-proofs/Explorers/", "Pictures-with-proofs/Inside-an-entry/",
         "Pictures-with-proofs/Escaping/"]
EXPLORERS = "Pictures-with-proofs/Explorers/"
ENTRY = "Pictures-with-proofs/Inside-an-entry/"
ODD = "Pictures-with-proofs/Escaping/"
FIGURE_PAGES = [p for p in PAGES if p != "Figures/"]
TIMEOUT = 10000


def current(page, fig):
    return page.evaluate(f"""() => {{
      const f = document.querySelector('figure#{fig}');
      const shown = [...f.querySelectorAll('li.pilean-explorer-frame')]
        .filter(li => li.offsetParent !== null);
      return shown.map(li => Number(li.dataset.index));
    }}""")


def view_box(page, fig):
    return page.evaluate(f"""() => document.querySelector(
      'figure#{fig} li.pilean-explorer-current svg').getAttribute('viewBox')""")


def width_of(box):
    return float(box.split()[2])


def new_page(browser, **kw):
    ctx = browser.new_context(**kw)
    ctx.add_init_script(REPORTS)
    ctx.set_default_timeout(TIMEOUT)
    return ctx, ctx.new_page()


def goto(page, url):
    page.goto(url)
    page.wait_for_load_state("networkidle")


def theme_checks(c, browser, base, shots):
    """The inline pictures' tint in both themes."""
    for scheme in ["light", "dark"]:
        ctx, page = new_page(browser, color_scheme=scheme, viewport={"width": 1100, "height": 900})
        goto(page, base + EXPLORERS)
        fill = page.evaluate("""() => getComputedStyle(document.querySelector(
          'figure#inline svg path[fill-opacity]')).fill""")
        c.check(f"{scheme}: the inline picture's tint follows the theme",
                ("rgb(0, 104, 166)" == fill) == (scheme == "light"), fill)
        reports = figure_reports(page)
        c.check(f"{scheme}: the explorers page has no content-policy report", not reports,
                str(reports))
        if shots:
            page.screenshot(path=f"{shots}/{scheme}-explorers.png", full_page=True)
        goto(page, base + ENTRY)
        fill = page.evaluate("""() => getComputedStyle(document.querySelector(
          'figure[id="3d-odd"] svg path[fill-opacity]')).fill""")
        c.check(f"{scheme}: the tint of a picture whose id starts with a digit follows the theme",
                ("rgb(0, 104, 166)" == fill) == (scheme == "light"), fill)
        ctx.close()


def control_checks(c, browser, base, shots):
    """The slider, the stepper, the status region, the keys and the inline links."""
    ctx, page = new_page(browser, viewport={"width": 1100, "height": 900})
    goto(page, base + EXPLORERS)
    c.check("the slider shows the poster frame only", current(page, "radius") == [2],
            str(current(page, "radius")))
    status0 = page.evaluate("window.__liveChanges.length")
    c.check("nothing is announced when the page loads", status0 == 0, str(status0))
    live = page.evaluate("""() => [...document.querySelectorAll('figure.pilean-figure-explorer')]
      .map(f => [...f.querySelectorAll('[aria-live], output, [role=status]')]
        .filter(e => e.getAttribute('aria-live') !== 'off').length)""")
    c.check("each explorer has one live region", all(n == 1 for n in live), str(live))
    page.evaluate("""() => { const s = document.querySelector('figure#radius input[type=range]');
      s.value = '4'; s.dispatchEvent(new Event('input', {bubbles: true})); }""")
    c.check("moving the slider changes the frame", current(page, "radius") == [4],
            str(current(page, "radius")))
    out = page.locator("figure#radius .pilean-explorer-value").inner_text()
    vt = page.locator("figure#radius input[type=range]").get_attribute("aria-valuetext")
    st = page.evaluate("window.__liveChanges.length")
    c.check("the slider says its value itself, no live region repeats it",
            out == "10/10" and vt == "10/10" and st == 0, f"{out} {vt} {st!r}")
    name = page.locator("figure#radius input[type=range]").get_attribute("aria-label")
    c.check("the slider's name says what it sets", name == "Value of r in Figure 1.4.1", name)
    page.locator("figure#radius input[type=range]").focus()
    page.keyboard.press("ArrowLeft")
    c.check("the slider works from the keyboard", current(page, "radius") == [3],
            str(current(page, "radius")))
    page.locator("figure#word [data-action=next]").click()
    counter = page.locator("figure#word .pilean-explorer-counter").inner_text()
    said = page.locator("figure#word .pilean-explorer-status").text_content()
    c.check("next shows the second step and says it once",
            current(page, "word") == [1] and counter == "Step 2 of 4"
            and said == "Step 2 of 4: a: a fifth turn about −1", f"{counter} / {said}")
    page.locator("figure#word [data-action=prev]").click()
    c.check("previous shows the first step again", current(page, "word") == [0])
    page.locator("figure#word [data-action=next]").focus()
    page.keyboard.press("Enter")
    caption = page.locator("figure#word .pilean-explorer-caption").inner_text()
    c.check("the stepper works from the keyboard, its caption shown",
            current(page, "word") == [1] and caption.startswith("a:"), caption)
    page.evaluate("window.__liveChanges = []")
    page.locator("figure#word [data-action=play]").click()
    page.wait_for_timeout(3000)
    pressed = page.locator("figure#word [data-action=play]").get_attribute("aria-pressed")
    moved = current(page, "word")
    page.locator("figure#word [data-action=play]").click()
    playing = page.evaluate("window.__liveChanges.length")
    c.check("while the steps play nothing is announced",
            pressed == "true" and moved != [1] and playing == 0, f"{pressed} {moved} {playing}")
    view = page.locator("figure#radius .pilean-explorer-view")
    box0 = view_box(page, "radius")
    view.focus()
    page.keyboard.press("+")
    box1 = view_box(page, "radius")
    page.keyboard.press("0")
    box2 = view_box(page, "radius")
    c.check("+ zooms the view and 0 resets it",
            width_of(box1) < width_of(box0) and box2 == box0, f"{box0} / {box1} / {box2}")
    page.evaluate("""() => { window.__prevented = [];
      window.addEventListener('keydown', e => window.__prevented.push(e.defaultPrevented)); }""")
    for key in ["Control+=", "Control+0", "Meta+=", "Alt+ArrowLeft"]:
        page.keyboard.press(key)
    kept = page.evaluate("window.__prevented")
    c.check("keys with Ctrl, Meta or Alt are left to the browser",
            view_box(page, "radius") == box0 and kept and not any(kept), str(kept))
    label = view.get_attribute("aria-label") or ""
    help_id = view.get_attribute("aria-describedby") or ""
    helped = page.evaluate("(id) => !!document.getElementById(id)", help_id) if help_id else False
    c.check("the view is named by the text alternative, without a doubled stop, and described",
            label.startswith("A window disk") and ".." not in label and helped, label)
    link = page.locator("figure#inline a.pilean-decl-link").first
    c.check("an element of the inline figure links to its declaration",
            link.get_attribute("href") == "lean:decl/Example.cubic"
            and link.get_attribute("aria-label") == "ζ^0")
    title = page.evaluate("""() => document.querySelector('figure#inline svg title').textContent""")
    c.check("an element's title is in the page (hover text)", title == "the window", title)
    labelled = page.evaluate("""() => { const f = document.querySelector('figure#radius');
      return f.getAttribute('role') === 'group' &&
        document.getElementById(f.getAttribute('aria-labelledby')) !== null; }""")
    c.check("the explorer is a group labelled by its caption", labelled)
    page.evaluate("""() => { const b = document.querySelector('figure#word .pilean-figure-number');
      b.setAttribute('onclick', 'void 0'); b.click(); }""")
    page.wait_for_timeout(100)
    kept = [r for r in figure_reports(page) if r["directive"] == "script-src-attr"]
    c.check("the report filter keeps an inline handler inside a figure", len(kept) == 1, str(kept))
    ctx.close()


def wheel_checks(c, browser, base, shots):
    """The wheel: the page scrolls; Ctrl and the wheel zoom, and a gesture under way keeps
    zooming."""
    ctx, page = new_page(browser, viewport={"width": 1100, "height": 900})
    goto(page, base + EXPLORERS)
    page.locator("figure#radius").scroll_into_view_if_needed()
    page.evaluate("window.scrollBy(0, -100)")
    vb = page.locator("figure#radius .pilean-explorer-view").bounding_box()
    page.mouse.move(vb["x"] + vb["width"] / 2, vb["y"] + vb["height"] / 2)
    y0, b0 = page.evaluate("scrollY"), view_box(page, "radius")
    page.mouse.wheel(0, 200)
    page.wait_for_timeout(300)
    y1, b1 = page.evaluate("scrollY"), view_box(page, "radius")
    c.check("the wheel over an explorer scrolls the page", y1 > y0 and b1 == b0,
            f"{y0}->{y1} {b0} {b1}")
    vb = page.locator("figure#radius .pilean-explorer-view").bounding_box()
    page.mouse.move(vb["x"] + vb["width"] / 2, vb["y"] + vb["height"] / 2)
    page.keyboard.down("Control")
    page.mouse.wheel(0, -100)
    page.keyboard.up("Control")
    page.wait_for_timeout(50)
    y2, b2 = page.evaluate("scrollY"), view_box(page, "radius")
    page.mouse.wheel(0, -60)
    page.wait_for_timeout(50)
    y3, b3 = page.evaluate("scrollY"), view_box(page, "radius")
    c.check("Ctrl and the wheel zoom the picture, not the page",
            width_of(b2) < width_of(b1) and y2 == y1, f"{b1} {b2} {y1}->{y2}")
    c.check("the wheel right after keeps zooming", width_of(b3) < width_of(b2) and y3 == y2,
            f"{b2} {b3}")
    page.wait_for_timeout(600)
    page.mouse.wheel(0, 120)
    page.wait_for_timeout(300)
    y4, b4 = page.evaluate("scrollY"), view_box(page, "radius")
    c.check("after a pause the wheel scrolls the page again", y4 > y3 and b4 == b3,
            f"{y3}->{y4}")
    ctx.close()


def size_checks(c, browser, base, shots):
    """Frames of different sizes keep their own view box; the script set up twice acts once."""
    ctx, page = new_page(browser, viewport={"width": 1100, "height": 900})
    goto(page, base + ENTRY)
    homes = page.evaluate("""() => [...document.querySelectorAll('figure#sizes li svg')]
      .map(s => s.getAttribute('data-view'))""")
    view = page.locator("figure#sizes .pilean-explorer-view")
    view.focus()
    page.keyboard.press("+")
    page.keyboard.press("0")
    page.locator("figure#sizes [data-action=next]").click()
    narrow = view_box(page, "sizes")
    c.check("a frame of another size keeps its own view box", narrow == homes[1],
            f"{narrow} / {homes}")
    view.focus()
    page.keyboard.press("+")
    zoomed = [page.evaluate(f"""() => document.querySelectorAll('figure#sizes li svg')[{i}]
      .getAttribute('viewBox')""") for i in range(3)]
    ratios = [width_of(z) / width_of(h) for z, h in zip(zoomed, homes)]
    c.check("the zoom is the same share of every frame", max(ratios) - min(ratios) < 1e-6
            and ratios[0] < 1, str(ratios))

    # Set up twice, the script acts once: its handlers are added once.
    page.evaluate("""() => new Promise(r => { const s = document.createElement('script');
      s.src = '-verso-data/pilean-explorer.js'; s.onload = r; document.head.append(s); })""")
    cdp = page.context.new_cdp_session(page)
    obj = cdp.send("Runtime.evaluate", {"expression":
                   "document.querySelector('figure#sizes .pilean-explorer-view')"})
    kinds = [x["type"] for x in cdp.send("DOMDebugger.getEventListeners",
             {"objectId": obj["result"]["objectId"]})["listeners"]]
    c.check("the script loaded twice adds its handlers once",
            kinds.count("wheel") == 1 and kinds.count("pointerdown") == 1, str(kinds))
    ctx.close()


def hostile_checks(c, browser, base, shots):
    """Hostile strings: shown as text, nothing runs."""
    ctx, page = new_page(browser, viewport={"width": 1100, "height": 900})
    goto(page, base + ODD)
    page.locator("figure#odd [data-action=next]").click()
    shown = page.evaluate("""() => { const f = document.querySelector('figure#odd');
      return [f.querySelector('.pilean-explorer-counter').textContent,
              f.querySelector('.pilean-explorer-caption').textContent,
              f.querySelector('.pilean-explorer-value').textContent,
              f.querySelector('.pilean-explorer-status').textContent]; }""")
    c.check("captions holding the label's separators are shown whole",
            shown == ["Step 2 of 2", "<img src=x onerror=alert(2)> & ' \"",
                      "1 · 2 = 3", "Step 2 of 2: <img src=x onerror=alert(2)> & ' \""],
            str(shown))
    page.evaluate("""() => { const s = document.querySelector('figure#odd input[type=range]');
      s.value = '1'; s.dispatchEvent(new Event('input', {bubbles: true})); }""")
    v = page.locator("figure#odd .pilean-explorer-value").text_content()
    c.check("a value holding markup is shown as text", v == "</style><script>alert(1)</script>", v)
    planted = page.evaluate("""() => [document.querySelectorAll('figure img[src=x], figure script')
      .length, window.__alerts.length]""")
    c.check("nothing a figure's strings hold runs or loads", planted == [0, 0], str(planted))
    ctx.close()


def noscript_checks(c, browser, base, shots):
    """Without script, and with reduced motion."""
    ctx = browser.new_context(java_script_enabled=False, viewport={"width": 1100, "height": 900})
    page = ctx.new_page()
    page.goto(base + EXPLORERS)
    shown = current(page, "radius")
    hidden = page.locator("figure#radius .pilean-explorer-controls").is_hidden()
    c.check("without script every frame is shown and the controls are hidden",
            shown == [0, 1, 2, 3, 4] and hidden, str(shown))
    quiet = page.evaluate("""() => [...document.querySelectorAll('.pilean-explorer-view')]
      .map(v => [v.tabIndex, v.getAttribute('role'), v.getAttribute('aria-label')])""")
    c.check("without script the view is no tab stop and promises nothing",
            all(q == [-1, None, None] for q in quiet), str(quiet))
    cells = page.evaluate("""() => [...document.querySelectorAll('figure#radius li')].map(li => {
      const r = li.getBoundingClientRect(); return [Math.round(r.left), Math.round(r.top),
        Math.round(r.width),
        li.querySelector('.pilean-explorer-frame-label').offsetHeight > 0]; })""")
    in_order = all((b[1] > a[1] + 16) or (abs(b[1] - a[1]) <= 16 and b[0] > a[0])
                   for a, b in zip(cells, cells[1:]))
    c.check("without script the frames are a grid in order, as many columns as fit, equal "
            "cells, each labelled",
            in_order and len({l for l, *_ in cells}) >= 2 and len({w for _, _, w, _ in cells}) == 1
            and all(l for *_, l in cells), str(cells))
    ctx.close()
    ctx = browser.new_context(java_script_enabled=False, viewport={"width": 360, "height": 800})
    page = ctx.new_page()
    page.goto(base + EXPLORERS)
    lefts = page.evaluate("""() => [...document.querySelectorAll('figure#radius li')]
      .map(li => Math.round(li.getBoundingClientRect().left))""")
    wide = page.evaluate("document.documentElement.scrollWidth - window.innerWidth")
    c.check("without script at 360 px the frames are one column within the page",
            len(set(lefts)) == 1 and wide <= 0, f"{lefts} {wide}")
    ctx.close()

    ctx = browser.new_context(reduced_motion="reduce")
    page = ctx.new_page()
    goto(page, base + EXPLORERS)
    c.check("reduced motion: no play button",
            page.locator("figure#word [data-action=play]").is_hidden())
    ctx.close()


def long_word_checks(c, browser, base, shots):
    """At 360 px: a word of 240 letters in a caption and in the figures page's list wraps within
    the page."""
    ctx = browser.new_context(viewport={"width": 360, "height": 800})
    page = ctx.new_page()
    word = "W" * 240
    goto(page, base + "Pictures-with-proofs/A-function/")
    got = page.evaluate("""w => { const cap = document.querySelector('.pilean-figure-caption');
      cap.append(' ' + w); return [document.documentElement.scrollWidth - window.innerWidth,
        cap.getBoundingClientRect().right <= window.innerWidth]; }""", word)
    c.check("360 px: a caption with a 240-letter word stays within the page",
            got[0] <= 0 and got[1], str(got))
    goto(page, base + "Figures/")
    got = page.evaluate("""w => { const t = document.querySelector('.pilean-figure-index li');
      t.querySelector('.pilean-index-title').append(' ' + w);
      const ol = document.querySelector('ol.pilean-figure-index');
      return [document.documentElement.scrollWidth - window.innerWidth,
        ol.scrollWidth - ol.clientWidth]; }""", word)
    c.check("360 px: the figures page with a 240-letter word in its list stays within the page",
            got[0] <= 0 and got[1] <= 0, str(got))
    ctx.close()
    for width in (360, 320):
        ctx = browser.new_context(viewport={"width": width, "height": 800})
        page = ctx.new_page()
        goto(page, base + EXPLORERS)
        got = page.evaluate("""w => { const a = document.querySelector(
          'figure#radius .pilean-explorer-axis-name'); a.textContent = w;
          const v = document.querySelector('figure#radius .pilean-explorer-value');
          v.textContent = w; const r = document.querySelector(
          'figure#radius .pilean-explorer-axis').getBoundingClientRect();
          return [document.documentElement.scrollWidth - window.innerWidth,
            r.right <= window.innerWidth]; }""", "n" * 36)
        c.check(f"{width} px: an explorer's axis with a 36-character name and value stays "
                "within the page", got[0] <= 0 and got[1], str(got))
        ctx.close()


def touch_checks(c, browser, base, shots):
    """At 360 px on a touch screen: the controls' sizes, a swipe, a pinch."""
    ctx, page = new_page(browser, viewport={"width": 360, "height": 800}, has_touch=True,
                         is_mobile=True, device_scale_factor=2)
    goto(page, base + EXPLORERS)
    narrow = page.evaluate("""() => [...document.querySelectorAll('figure#inline svg')]
      .filter(s => s.getBoundingClientRect().width > 0).map(s => s.id)""")
    c.check("360 px: the inline figure shows its narrow rendition",
            narrow == ["inline-svg-narrow"], str(narrow))
    sizes = page.evaluate("""() => [...document.querySelectorAll(
        '.pilean-explorer-controls button, .pilean-explorer-controls input')]
      .filter(e => e.getClientRects().length).map(e => { const b = e.getBoundingClientRect();
        return [e.getAttribute('data-action') || e.type, b.width, b.height]; })""")
    c.check("360 px: every control is at least 44 by 44 pixels",
            bool(sizes) and all(w >= 44 and h >= 44 for _, w, h in sizes), str(sizes))
    icons = page.evaluate("""() => [...document.querySelectorAll(
      '[data-action=prev] svg, [data-action=next] svg')]
      .every(s => s.getBoundingClientRect().width >= 16)""")
    c.check("360 px: the step buttons' icons are drawn large enough", icons)
    if shots:
        page.screenshot(path=f"{shots}/w360-explorers.png", full_page=True)

    # One finger scrolls the page; two fingers zoom the picture.
    cdp = ctx.new_cdp_session(page)
    page.locator("figure#radius").scroll_into_view_if_needed()
    vb = page.locator("figure#radius .pilean-explorer-view").bounding_box()
    cx, cy = vb["x"] + vb["width"] / 2, vb["y"] + vb["height"] / 2
    y0, b0 = page.evaluate("scrollY"), view_box(page, "radius")
    cdp.send("Input.synthesizeScrollGesture", {"x": cx, "y": cy, "yDistance": -250,
             "gestureSourceType": "touch", "speed": 800})
    page.wait_for_timeout(400)
    y1, b1 = page.evaluate("scrollY"), view_box(page, "radius")
    c.check("a one-finger swipe over an explorer scrolls the page", y1 > y0 and b1 == b0,
            f"{y0}->{y1} {b0} {b1}")
    vb = page.locator("figure#radius .pilean-explorer-view").bounding_box()
    cx, cy = vb["x"] + vb["width"] / 2, vb["y"] + vb["height"] / 2
    y1 = page.evaluate("scrollY")

    def touch(kind, d):
        pts = [] if kind == "touchEnd" else [
            {"x": cx - d, "y": cy, "id": 1}, {"x": cx + d, "y": cy, "id": 2}]
        cdp.send("Input.dispatchTouchEvent", {"type": kind, "touchPoints": pts})

    touch("touchStart", 20)
    for d in range(24, 80, 4):
        touch("touchMove", d)
    touch("touchEnd", 0)
    page.wait_for_timeout(200)
    y2, b2 = page.evaluate("scrollY"), view_box(page, "radius")
    c.check("two fingers spreading zoom the picture", width_of(b2) < width_of(b1),
            f"{b1} -> {b2}, scroll {y1}->{y2}")
    ctx.close()

    ctx = browser.new_context(java_script_enabled=False, viewport={"width": 360, "height": 800},
                              has_touch=True, is_mobile=True)
    page = ctx.new_page()
    page.goto(base + EXPLORERS)
    cdp = ctx.new_cdp_session(page)
    page.locator("figure#radius").scroll_into_view_if_needed()
    vb = page.locator("figure#radius li").first.bounding_box()
    y0 = page.evaluate("scrollY")
    cdp.send("Input.synthesizeScrollGesture", {"x": vb["x"] + vb["width"] / 2,
             "y": vb["y"] + 20, "yDistance": -250, "gestureSourceType": "touch", "speed": 800})
    page.wait_for_timeout(400)
    y1 = page.evaluate("scrollY")
    c.check("without script a one-finger swipe over the frames scrolls the page", y1 > y0,
            f"{y0}->{y1}")
    ctx.close()


def strict_style_checks(c, browser, site):
    """A policy that allows the pictures' style elements by hash only."""
    server, base = serve(site, styles="hashes")
    for scheme in ["light", "dark"]:
        ctx, page = new_page(browser, color_scheme=scheme, viewport={"width": 1100, "height": 900})
        goto(page, base + EXPLORERS)
        fill = page.evaluate("""() => getComputedStyle(document.querySelector(
          'figure#inline svg path[fill-opacity]')).fill""")
        styles = [r for r in figure_reports(page)
                  if r["directive"].startswith("style") and r["inFigure"]]
        c.check(f"{scheme}: style elements allowed by hash: the inline tint follows the theme",
                ("rgb(0, 104, 166)" == fill) == (scheme == "light") and not styles,
                f"{fill} {styles}")
        ctx.close()
    server.shutdown()


CENTRED = """(sel) => {
  const out = [];
  for (const f of document.querySelectorAll('figure.pilean-figure')) {
    if (!f.getClientRects().length) continue;
    const fr = f.getBoundingClientRect();
    const box = f.parentElement.getBoundingClientRect();
    const parts = [...f.querySelectorAll(sel)].filter(e => e.getClientRects().length &&
      e.getBoundingClientRect().width > 0);
    if (fr.left < box.left - 0.5 || fr.right > box.right + 0.5)
      out.push([f.id, 'figure', fr.left, fr.right, box.left, box.right]);
    // Every line of the caption's text is centred too.
    for (const cap of f.querySelectorAll('figcaption')) {
      const cr = cap.getBoundingClientRect();
      const rows = [];
      const boxes = [];
      const walk = document.createTreeWalker(cap, NodeFilter.SHOW_TEXT);
      for (let n = walk.nextNode(); n; n = walk.nextNode()) {
        const p = n.parentElement;
        if (!n.textContent.trim() || !p.getClientRects().length) continue;
        if (p.closest('svg, .pilean-fingerprint, .bp_math')) continue;
        const r = document.createRange(); r.selectNodeContents(n);
        boxes.push(...r.getClientRects());
      }
      for (const e of cap.querySelectorAll('.bp_math, svg, .pilean-fingerprint'))
        if (!e.parentElement.closest('svg, .bp_math')) boxes.push(...e.getClientRects());
      for (const q of boxes) {
        if (q.width < 1) continue;
        const mid = (q.top + q.bottom) / 2;
        const row = rows.find(w => mid > w.top && mid < w.bottom);
        if (row) { row.l = Math.min(row.l, q.left); row.r = Math.max(row.r, q.right); }
        else rows.push({top: q.top, bottom: q.bottom, l: q.left, r: q.right});
      }
      for (const {l, r} of rows)
        if (Math.abs((l - cr.left) - (cr.right - r)) > 3)
          out.push([f.id, 'caption line', Math.round(l - cr.left), Math.round(cr.right - r)]);
    }
    for (const e of parts) {
      const r = e.getBoundingClientRect();
      const l = r.left - fr.left, rt = fr.right - r.right;
      if (l < -0.5 || rt < -0.5 || Math.abs(l - rt) > 1.5)
        out.push([f.id, e.tagName + '.' + (e.getAttribute('class') || ''), Math.round(l),
                  Math.round(rt)]);
    }
  }
  return out;
}"""
PARTS = ("img.pilean-figure-img, .pilean-figure-stack, svg.pilean-inline-svg, "
         ".pilean-explorer-controls, figcaption, .pilean-figure-source")


def centring_checks(c, browser, base, label, widths, pages):
    for width in widths:
        ctx, page = new_page(browser, viewport={"width": width, "height": 900})
        for url in pages:
            goto(page, base + url)
            bad = page.evaluate(CENTRED, PARTS)
            c.check(f"{label} {width} px: {url}: every figure's parts centred and within it",
                    not bad, str(bad[:4]))
        ctx.close()


def column_checks(c, browser, base, shots):
    """Figures inside a Blueprint entry of the side-by-side layout sit in its text column."""
    for width in [1400, 1100]:
        ctx, page = new_page(browser, viewport={"width": width, "height": 900})
        goto(page, base + ENTRY)
        col = page.evaluate("""() => { const f = document.querySelector('figure#sizes');
          const col = f.closest('.bp_sbs_informal');
          if (!col) return null;
          const a = col.getBoundingClientRect(), b = f.getBoundingClientRect();
          return [a.width, b.left >= a.left - 0.5 && b.right <= a.right + 0.5]; }""")
        c.check(f"side by side {width} px: the explorer is in the entry's text column",
                col is not None and col[1] and col[0] < width / 2, str(col))
        bad = page.evaluate(CENTRED, PARTS)
        c.check(f"side by side {width} px: the figures in the column are centred within it",
                not bad, str(bad[:4]))
        if shots and width == 1100:
            page.screenshot(path=f"{shots}/side-by-side-entry.png", full_page=True)
        ctx.close()


def link_checks(c, browser, sites):
    """The three link modes, and links never nested."""
    for mode, site in sites.items():
        if site is None:
            continue
        server, base = serve(site)
        ctx, page = new_page(browser, viewport={"width": 1100, "height": 900})
        nested = 0
        for url in PAGES:
            goto(page, base + url)
            nested += page.evaluate("document.querySelectorAll('a a').length")
        c.check(f"{mode}: no link inside another", nested == 0, str(nested))
        goto(page, base + EXPLORERS)
        hrefs = page.evaluate("""() => [...document.querySelectorAll('figure a')]
          .filter(a => !a.classList.contains('pilean-repo-link'))
          .map(a => a.getAttribute('href'))""")
        if mode == "site":
            c.check("site: no lean: link in a figure",
                    bool(hrefs) and not any(h.startswith("lean:") for h in hrefs), str(hrefs[:3]))
        if mode == "none":
            c.check("none: no link in a figure but the repository's", hrefs == [], str(hrefs[:3]))
            title = page.evaluate("""() => document.querySelector(
              'figure#inline svg g[data-lean-decl] title').textContent""")
            stops = page.evaluate("""() => [...document.querySelectorAll('figure#inline svg *')]
              .filter(e => e.tabIndex >= 0).length""")
            c.check("none: an element keeps its hover text and is no tab stop",
                    title == "ζ^0" and stops == 0, f"{title} {stops}")
        if mode in ("site", "side-by-side"):
            for fig, url, sel in [
                    ("inline", EXPLORERS, "figure#inline a.pilean-decl-link"),
                    ("theorem", PAGES[0], "figure#cubic .pilean-figure-source a.pilean-site-link")]:
                goto(page, base + url)
                link = page.locator(sel).first
                href = link.get_attribute("href") or ""
                link.click()
                page.wait_for_load_state("networkidle")
                frag = page.url.split("#", 1)[1] if "#" in page.url else ""
                found = page.evaluate("(id) => !!document.getElementById(decodeURIComponent(id))",
                                      frag)
                c.check(f"{mode}: a click on the {fig} link reaches an existing anchor",
                        bool(frag) and found and not href.startswith("lean:"),
                        f"{href} -> {page.url}")
            goto(page, base + PAGES[0])
            own = page.evaluate("""() => document.querySelectorAll(
              'figure#cubic .pilean-source-item:first-child a.pilean-site-link').length""")
            c.check(f"{mode}: the figure's own declaration does not link to the figure itself",
                    own == 0, str(own))
            goto(page, base + "Figures/")
            src = page.locator(".pilean-index-facts dd a.pilean-site-link").first
            href = src.get_attribute("href") or ""
            src.click()
            page.wait_for_load_state("networkidle")
            frag = page.url.split("#", 1)[1] if "#" in page.url else ""
            found = page.evaluate("(id) => !!document.getElementById(decodeURIComponent(id))", frag)
            c.check(f"{mode}: the figures page links a declaration to its place", found,
                    f"{href} -> {page.url}")
        ctx.close()
        server.shutdown()


class Checks:
    def __init__(self):
        self.failed = 0
        self.count = 0

    def section(self, name, fn, *args):
        """Runs a group of checks; one that stops with an error counts as a failure."""
        try:
            fn(*args)
        except Exception as e:  # noqa: BLE001 - a check that cannot run is a failed check
            self.check(f"{name} ran to its end", False, str(e).splitlines()[0])

    def check(self, name, ok, detail=""):
        self.count += 1
        if ok:
            print(f"ok: {name}")
        else:
            self.failed += 1
            print(f"FAIL: {name} {detail}")


def shown_pictures(page):
    return page.evaluate("""() => [...document.querySelectorAll('figure.pilean-figure')].map(f => {
      const imgs = [...f.querySelectorAll('img')].filter(i => i.offsetParent !== null);
      return {id: f.id, shown: imgs.map(i => i.currentSrc || i.src),
              loaded: imgs.every(i => i.complete && i.naturalWidth > 0)};
    })""")


def option(args, name):
    return args[args.index(name) + 1] if name in args else None


def main(argv):
    site = argv[0]
    rest = argv[1:]
    shots = rest[0] if rest and not rest[0].startswith("--") else None
    sites = {"ideil": site, "site": option(rest, "--site-links"),
             "none": option(rest, "--no-links"), "side-by-side": option(rest, "--side-by-side")}
    server, base = serve(site)
    c = Checks()
    with sync_playwright() as p:
        browser = p.chromium.launch()
        for scheme in ["light", "dark"]:
            ctx, page = new_page(browser, color_scheme=scheme,
                                 viewport={"width": 1100, "height": 900})
            for url in PAGES[:4]:
                goto(page, base + url)
                for fig in shown_pictures(page):
                    c.check(f"{scheme}: {fig['id']} shows one picture, loaded",
                            len(fig["shown"]) == 1 and fig["loaded"], str(fig))
                    if fig["id"] != "circle" and fig["shown"]:
                        dark = fig["shown"][0].endswith("-dark.svg")
                        c.check(f"{scheme}: {fig['id']} follows the system's scheme",
                                dark == (scheme == "dark"), fig["shown"][0])
            for url in PAGES:
                goto(page, base + url)
                reports = figure_reports(page)
                c.check(f"{scheme}: {url} has no content-policy report", not reports, str(reports))
                if shots:
                    page.screenshot(path=f"{shots}/{scheme}-{url.strip('/').replace('/', '-')}.png",
                                    full_page=True)
            # The page's own switch wins over the system.
            page.goto(base + PAGES[0])
            other = "light" if scheme == "dark" else "dark"
            page.evaluate(f"document.documentElement.setAttribute('data-theme', '{other}')")
            shown = shown_pictures(page)[0]["shown"][0]
            c.check(f"{scheme} system, data-theme={other}: the page's theme wins",
                    shown.endswith("-dark.svg") == (other == "dark"), shown)
            ctx.close()

        ctx, page = new_page(browser, viewport={"width": 1100, "height": 900})
        page.goto(base + PAGES[0])
        fig = page.locator("figure#cubic")
        c.check("the figure has its number", "Figure 1.1.1" in fig.inner_text())
        lean_link = fig.locator(".pilean-figure-source a.pilean-lean-link").first
        text = fig.locator(".pilean-figure-source .pilean-lean-text").first
        c.check("without data-lean-links the declaration is plain text",
                not lean_link.is_visible() and text.is_visible())
        page.evaluate("document.documentElement.setAttribute('data-lean-links', '')")
        c.check("with data-lean-links the declaration is a lean: link",
                lean_link.is_visible() and not text.is_visible()
                and lean_link.get_attribute("href") == "lean:decl/Example.cubicPlot")
        hrefs = fig.locator("a.pilean-lean-link").evaluate_all("as => as.map(a => a.href)")
        c.check("the theorem's lean: link", "lean:decl/Example.cubicPlot_spec" in hrefs, str(hrefs))
        repo = fig.locator("a.pilean-repo-link").first.get_attribute("href") or ""
        c.check("the source links the repository at the commit",
                re.fullmatch(r"https://github\.com/[^/]+/PILean/blob/[0-9a-f]{40}/"
                             r"verso/example/Example/Figures\.lean#L\d+", repo) is not None, repo)
        fp = fig.locator(".pilean-fingerprint")
        full = fp.get_attribute("title") or ""
        c.check("the fingerprint is whole in the text and the tooltip",
                re.fullmatch(r"[0-9a-f]{64}", full) is not None and fp.inner_text() == full)
        c.check("the fingerprint is shown shortened",
                fp.evaluate("e => e.scrollWidth > e.clientWidth"))
        img = fig.locator("img").first
        c.check("the picture has its text alternative and tooltip",
                (img.get_attribute("alt") or "").startswith("The cubic")
                and "Example.cubicPlot" in (img.get_attribute("title") or ""))
        ref = page.locator("a.pilean-figref").first
        c.check("a reference names and links the figure",
                ref.inner_text() == "Figure 1.1.1" and ref.get_attribute("href").endswith("#cubic"))

        page.goto(base + "Figures/")
        items = page.locator(".pilean-figure-index > li")
        c.check("the figures page lists ten figures", items.count() == 10, str(items.count()))
        thumbs = page.evaluate("""() => [...document.querySelectorAll('.pilean-index-thumb img')]
            .every(i => i.complete && i.naturalWidth > 0)""")
        c.check("the figures page's pictures load", thumbs)
        files = page.locator(".pilean-index-files a").evaluate_all("as => as.map(a => a.href)")
        statuses = [ctx.request.get(h).status for h in files]
        c.check("every file the figures page links is served", all(s == 200 for s in statuses),
                str(statuses))
        manifest = page.locator(".pilean-figure-index-intro a").get_attribute("href")
        c.check("the manifest is linked and served",
                ctx.request.get(base + manifest).json()["format"] == "pilean-manifest-1")
        first = items.first.locator(".pilean-index-title a").get_attribute("href")
        page.goto(base + first)
        c.check("the figures page links the figure itself",
                page.locator("figure#cubic").count() == 1 and page.url.endswith("#cubic"))
        ctx.close()

        for motion, expect in [("reduce", "-poster.png"), ("no-preference", ".svg")]:
            ctx = browser.new_context(reduced_motion=motion)
            page = ctx.new_page()
            goto(page, base + "Pictures-with-proofs/Motion/")
            src = page.locator("figure#circle img").evaluate("i => i.currentSrc")
            c.check(f"reduced motion {motion}: the animation shows {expect}", src.endswith(expect),
                    src)
            ctx.close()

        for part in [theme_checks, control_checks, wheel_checks, size_checks, hostile_checks,
                     noscript_checks, touch_checks, long_word_checks]:
            c.section(part.__name__, part, c, browser, base, shots)
        c.section("strict styles", strict_style_checks, c, browser, site)
        c.section("centring", centring_checks, c, browser, base, "stacked", [1100, 360],
                  FIGURE_PAGES)
        if sites["side-by-side"]:
            sbs_server, sbs_base = serve(sites["side-by-side"])
            c.section("column", column_checks, c, browser, sbs_base, shots)
            c.section("side-by-side centring", centring_checks, c, browser, sbs_base,
                      "side by side", [1400, 360], FIGURE_PAGES)
            sbs_server.shutdown()
        c.section("links", link_checks, c, browser, sites)

        for width in [320, 360, 375, 600]:
            ctx = browser.new_context(viewport={"width": width, "height": 800})
            page = ctx.new_page()
            for url in PAGES:
                goto(page, base + url)
                wide = page.evaluate("document.documentElement.scrollWidth - window.innerWidth")
                c.check(f"{width} px: {url} does not scroll sideways", wide <= 0, f"{wide} px")
                if shots and width == 375:
                    page.screenshot(path=f"{shots}/narrow-{url.strip('/').replace('/', '-')}.png",
                                    full_page=True)
            ctx.close()
        browser.close()
    server.shutdown()
    print(f"browser: {c.count - c.failed} of {c.count} hold")
    return 1 if c.failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
