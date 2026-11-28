# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
"""Checks the example site's figures in a headless Chromium (Playwright).

    python3 -I tests/browser_check.py SITE [SHOTS] [--site-links DIR] [--no-links DIR]
        [--side-by-side DIR] [--manual DIR] [--motions DIR] [--workers N]

SITE is the generator's `html-multi` folder, built with `--figure-repo` and the default link mode
(`ideil`); SHOTS, if given, is a folder for screenshots. The other folders are the same site
built with `--figure-lean-links site`, with `--figure-lean-links none`, and with
`--side-by-side --figure-lean-links site`; `--manual` names the Manual adapter's example
(`pilean-verso-manual-example`), and `--motions` the expectations of the motions of both examples
(the example's `example-test --motion-out DIR` and the Manual
adapter's `pilean-verso-manual-test --motion-out DIR`, into one folder). The checks of a folder not
given are skipped, but the motions are checked on every page that shows one (`--workers N` pages at
a time, each in a process with its own Chromium; one by default), and a motion without
its expectations fails (PILean's `tools/site/motion_browser.py`).

Each site is served on 127.0.0.1 with a strict content policy: scripts only from the site's files
and the inline scripts of the head (by hash), no inline event handlers, no plug-ins, nothing from
elsewhere. Checked: every picture loads in the light and the dark theme and the right one is shown;
the source line's links, the link to the figure's page landing on the anchor at its start with the
title in view and nothing highlighted, and the anchor adding no space above the picture (in both
adapters' examples); the figures page; the still frame under reduced motion; no horizontal scrolling
at narrow widths; no content-policy report about a figure. For the explorers: the sliders (one for
each parameter of a family of two) and the stepper change the frame (by pointer and by keyboard) and
say what they show from the frames' data, whatever the captions hold; one status region speaks, only
when asked; the page scrolls under a wheel or a one-finger swipe, the picture zooms under Ctrl and
the wheel or two fingers; frames of different sizes keep their own view; the script set up twice
acts once; the controls are large enough to touch; an inline element carries its title and its link;
the inline tint follows the theme, also for an id that starts with a digit, and under a policy that
allows the pictures' style elements by hash only; without script every frame is a grid cell in order
after the poster, which comes first across the width, and nothing is focusable; reduced motion has
no play button; at 360 px the narrow rendition is shown. The three link modes: `lean:` links, links
into the site that a click follows to an existing anchor (also in the side-by-side layout), and no
links. Everything a figure shows is centred in its container and stays within it: wide, in the
narrow column of the side-by-side layout, and at 360 px, also with a word of 240 letters in a
caption and in the figures page's list. Hostile captions, names and ids show as text and run
nothing.
"""

import os
import re
import sys

# PILean's site checks (tools/site), which this script runs on the example as one site of many
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..",
                                "tools", "site"))

from playwright.sync_api import sync_playwright  # noqa: E402

import motion_browser  # noqa: E402
from site_browser import Checks, figure_reports, goto, launch, new_page, serve  # noqa: E402

PAGES = ["Pictures-with-proofs/A-function/", "Pictures-with-proofs/Data/",
         "Pictures-with-proofs/A-relation/", "Pictures-with-proofs/Motion/", "Figures/",
         "Pictures-with-proofs/Explorers/", "Pictures-with-proofs/Inside-an-entry/",
         "Pictures-with-proofs/Escaping/"]
EXPLORERS = "Pictures-with-proofs/Explorers/"
ENTRY = "Pictures-with-proofs/Inside-an-entry/"
ODD = "Pictures-with-proofs/Escaping/"
FIGURE_PAGES = [p for p in PAGES if p != "Figures/"]


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
    # a family of two parameters: a slider for each, the second played
    c.check("a family of two parameters shows its poster frame", current(page, "family") == [4],
            str(current(page, "family")))
    names = page.evaluate("""() => [...document.querySelectorAll(
      'figure#family input[type=range]')].map(s => [s.dataset.axis, s.getAttribute('aria-label'),
      s.getAttribute('aria-valuetext')])""")
    c.check("a family of two parameters has a slider for each, named for what it sets",
            names == [["value", "Value of r in Figure 1.4.3", "8/10"],
                      ["step", "Value of c in Figure 1.4.3", "1/4"]], str(names))
    page.evaluate("""() => {
      const s = document.querySelector('figure#family input[data-axis=step]');
      s.value = '2'; s.dispatchEvent(new Event('input', {bubbles: true})); }""")
    shown = page.locator("figure#family .pilean-explorer-step-value").inner_text()
    c.check("the second slider moves the second parameter", current(page, "family") == [5]
            and shown == "2/4", f"{current(page, 'family')} {shown}")
    page.locator("figure#family [data-action=next]").click()
    said = page.locator("figure#family .pilean-explorer-status").text_content()
    vt = page.locator("figure#family input[data-axis=step]").get_attribute("aria-valuetext")
    c.check("next moves the second parameter round and says its value",
            current(page, "family") == [3] and said == "c = 0/4" and vt == "0/4",
            f"{current(page, 'family')} {said} {vt}")
    page.locator("figure#family input[data-axis=value]").focus()
    page.keyboard.press("ArrowRight")
    c.check("the first slider keeps the second parameter", current(page, "family") == [6],
            str(current(page, "family")))
    play = page.locator("figure#family [data-action=play]").get_attribute("aria-label")
    c.check("the play button names the parameter it plays", play == "Play c", str(play))
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
        li.querySelector('.pilean-explorer-frame-label').offsetHeight > 0,
        li.hasAttribute('data-poster')]; })""")
    poster = [x for x in cells if x[4]]
    rest = [x for x in cells if not x[4]]
    in_order = all((b[1] > a[1] + 16) or (abs(b[1] - a[1]) <= 16 and b[0] > a[0])
                   for a, b in zip(rest, rest[1:]))
    c.check("without script the poster comes first across the width, the other frames follow "
            "in a grid in order, as many columns as fit, equal cells, each labelled",
            len(poster) == 1 and all(poster[0][1] < x[1] for x in rest) and
            all(poster[0][2] > x[2] for x in rest) and
            in_order and len({l for l, *_ in rest}) >= 2 and len({w for _, _, w, *_ in rest}) == 1
            and all(x[3] for x in cells), str(cells))
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


PICTURE_PAGES = ["Figures/Example.cubicPlot/", "Figures/Example.circleAnimation/",
                 "Figures/Example.radiusExplorer/", "Figures/Example.divisorHasse/",
                 "Figures/Example.reductionSquare/", "Figures/Example.sketch/"]


def odd_page(base, ctx):
    """The address of the page of the figure whose name holds markup, from the figures page."""
    page = ctx.new_page()
    goto(page, base + "Figures/")
    hrefs = page.locator("a.pilean-page-link").evaluate_all("as => as.map(a => a.href)")
    page.close()
    odd = [h for h in hrefs if "Example._hasse_" in h]
    return odd[0].split("#")[0] if odd else None


def figure_page_checks(c, browser, base, shots):
    """The figures' pages: both themes at three widths, pictures and files, no request leaving
    the site, no console error, every link served, the keyboard alone, no script, reduced motion,
    hostile names."""
    ctx0 = browser.new_context()
    odd = odd_page(base, ctx0)
    ctx0.close()
    c.check("the figures page links the page of the name with markup", odd is not None)
    urls = [base + p for p in PICTURE_PAGES] + ([odd] if odd else [])
    for scheme in ["light", "dark"]:
        for width in [360, 768, 1440]:
            ctx, page = new_page(browser, color_scheme=scheme,
                                 viewport={"width": width, "height": 900})
            outside, errors = [], []
            page.on("request", lambda r: None if r.url.startswith(base) else outside.append(r.url))
            # the policy's own reports of Verso's inline handler outside the figures are counted
            # by figure_reports, which keeps those inside a figure or a figure's page
            page.on("console", lambda m: errors.append(m.text) if m.type == "error" and
                    not m.text.startswith("Executing inline event handler violates") else None)
            page.on("pageerror", lambda e: errors.append(str(e)))
            for url in urls:
                goto(page, url)
                name = url[len(base):]
                imgs = page.evaluate("""() => [...document.querySelectorAll(
                  '.pilean-page-picture img')].filter(i => i.offsetParent !== null)
                  .map(i => [i.currentSrc || i.src, i.complete && i.naturalWidth > 0])""")
                if "radiusExplorer" not in url:
                    c.check(f"{scheme} {width}: {name} shows one picture of its theme, loaded",
                            len(imgs) == 1 and imgs[0][1] and
                            (imgs[0][0].endswith("-dark.svg") == (scheme == "dark")
                             or "circleAnimation" in url), str(imgs))
                wide = page.evaluate("document.documentElement.scrollWidth - window.innerWidth")
                c.check(f"{scheme} {width}: {name} does not scroll sideways", wide <= 0,
                        f"{wide} px")
                reports = figure_reports(page)
                c.check(f"{scheme} {width}: {name} has no content-policy report", not reports,
                        str(reports))
                if shots and url == base + "Figures/Example.cubicPlot/" and width in [360, 1440]:
                    tag = f"{scheme}-{width}"
                    page.screenshot(path=f"{shots}/page-top-{tag}.png")
                    for part, sel in [("standing", ".pilean-page-standing"),
                                      ("code", ".pilean-page-codes"),
                                      ("provenance", ".pilean-page-provenance")]:
                        page.locator(sel).first.scroll_into_view_if_needed()
                        page.wait_for_timeout(300)
                        page.screenshot(path=f"{shots}/page-{part}-{tag}.png")
            c.check(f"{scheme} {width}: the pages ask nothing of another site", not outside,
                    str(outside[:3]))
            c.check(f"{scheme} {width}: the pages log no console error", not errors,
                    str(errors[:3]))
            ctx.close()
    ctx, page = new_page(browser, viewport={"width": 1100, "height": 900})
    bad = []
    for url in urls:
        goto(page, url)
        hrefs = page.evaluate("""() => [...document.querySelectorAll(
          '.pilean-figure-page a[href]')].map(a =>
            new URL(a.getAttribute('href'), document.baseURI).href)""")
        for h in sorted(set(hrefs)):
            if h.startswith(base):
                status = ctx.request.get(h.split("#")[0]).status
                if status != 200:
                    bad.append((h, status))
    c.check("every link of the pages into the site is served", not bad, str(bad[:5]))
    # The page's look with no fragment, then after a click on a link to it: the link lands on
    # the empty anchor at the start of the page, the page's title stays in view, and nothing on
    # the page takes the site's highlight of a link's target.
    look = """() => { const p = document.querySelector('.pilean-figure-page');
      const s = getComputedStyle(p);
      return [s.backgroundColor, s.backgroundImage, s.boxShadow, s.outlineStyle]; }"""
    for start, sel, scheme in [(base + PAGES[0], "figure#cubic a.pilean-page-link", "light"),
                               (base + "Figures/", "a.pilean-page-link", "dark")]:
        sctx, spage = new_page(browser, viewport={"width": 1100, "height": 900},
                               color_scheme=scheme)
        goto(spage, start)
        href = spage.locator(sel).first.get_attribute("href") or ""
        goto(spage, base + href.split("#")[0])
        plain = spage.evaluate(look)
        goto(spage, start)
        spage.locator(sel).first.click()
        spage.wait_for_load_state("networkidle")
        spage.wait_for_timeout(150)
        frag = spage.url.split("#", 1)[1] if "#" in spage.url else ""
        landed = spage.evaluate("""(id) => {
          const e = document.getElementById(decodeURIComponent(id));
          if (!e) return null;
          const r = e.getBoundingClientRect(), s = getComputedStyle(e);
          const page = document.querySelector('.pilean-figure-page');
          const h1 = document.querySelector('main h1');
          return {anchor: e.classList.contains('pilean-figure-page-anchor'),
                  first: page !== null && page.firstElementChild === e,
                  size: [r.width, r.height],
                  look: [s.backgroundColor, s.backgroundImage, s.boxShadow, s.outlineStyle],
                  title: h1 ? Math.round(h1.getBoundingClientRect().top) : null}; }""", frag)
        after = spage.evaluate(look)
        where = start[len(base):] or "the start"
        c.check(f"{scheme}: a page link from {where} lands on the anchor at the start of the page",
                bool(frag) and landed is not None and landed["anchor"] and landed["first"] and
                landed["size"] == [0, 0], f"{href} -> {spage.url}: {landed}")
        c.check(f"{scheme}: after a page link from {where} nothing on the page is highlighted",
                landed is not None and after == plain and
                landed["look"] == ["rgba(0, 0, 0, 0)", "none", "none", "none"],
                f"{plain} -> {after}; anchor {landed and landed['look']}")
        c.check(f"{scheme}: after a page link from {where} the page's title is in view",
                landed is not None and landed["title"] is not None and 0 <= landed["title"] < 900,
                str(landed and landed["title"]))
        sctx.close()
    goto(page, base + "Figures/Example.cubicPlot/")
    text = " ".join(page.locator(".pilean-page-standing").inner_text().split())
    c.check("a linked figure's page names its linked theorem and shows the statement",
            "Linked theorem: Example.cubicPlot_spec" in text and
            "it did not check what Example.cubicPlot_spec says." in text and
            "cubicPlot.panels" in text.replace(" ", ""), text[:200])
    goto(page, base + "Figures/Example.sketch/")
    text = page.locator(".pilean-figure-page").inner_text()
    c.check("an illustration's page says so and never names a linked theorem",
            "Illustration: no theorem is linked to it" in text and
            "Linked theorem" not in text)
    if odd:
        goto(page, odd)
        title = " ".join(page.locator("h1").all_inner_texts())
        planted = page.evaluate("""() => [document.querySelectorAll(
          '.pilean-figure-page script, .pilean-figure-page b').length, window.__alerts.length]""")
        c.check("the page of a name with markup shows it as text, and nothing runs",
                'Example.«hasse <b>"&\'»' in title and planted == [0, 0], f"{title} {planted}")
    ctx.close()
    # the keyboard alone: every download, the more-list and the source links can be reached
    ctx, page = new_page(browser, viewport={"width": 1100, "height": 900})
    goto(page, base + "Figures/Example.cubicPlot/")
    want = page.evaluate("""() => new Set([...document.querySelectorAll(
      '.pilean-figure-page a[href], .pilean-figure-page summary')]
      .filter(e => e.getClientRects().length > 0)
      .map(e => e.tagName + ':' + (e.getAttribute('href') || e.textContent).slice(0, 80))).size""")
    reached = set()
    for _ in range(400):
        page.keyboard.press("Tab")
        info = page.evaluate("""() => { const e = document.activeElement;
          if (!e || !e.closest('.pilean-figure-page')) return null;
          const r = e.getBoundingClientRect();
          return [e.tagName + ':' + (e.getAttribute('href') || e.textContent).slice(0, 80),
                  r.width > 0 && r.height > 0]; }""")
        if info:
            reached.add(info[0])
            if not info[1]:
                c.check("every element the keyboard reaches on a page is visible", False, info[0])
                break
    c.check("the keyboard alone reaches every link of a figure's page", len(reached) >= want,
            f"{len(reached)} of {want}")
    ctx.close()
    # no script, and reduced motion
    ctx = browser.new_context(java_script_enabled=False, viewport={"width": 1100, "height": 900})
    page = ctx.new_page()
    page.goto(base + "Figures/Example.cubicPlot/")
    loaded = page.evaluate("""() => [...document.querySelectorAll('.pilean-page-picture img')]
      .filter(i => i.offsetParent !== null).every(i => i.complete && i.naturalWidth > 0)""")
    words = page.locator(".pilean-page-standing").inner_text()
    c.check("without script a page shows its picture and its standing",
            loaded and "Linked theorem" in words)
    page.goto(base + "Figures/Example.radiusExplorer/")
    c.check("without script an explorer's page lists its frames",
            page.locator(".pilean-figure-page li.pilean-explorer-frame").count() == 5)
    ctx.close()
    ctx = browser.new_context(reduced_motion="reduce")
    page = ctx.new_page()
    goto(page, base + "Figures/Example.circleAnimation/")
    src = page.locator(".pilean-page-picture img").first.evaluate("i => i.currentSrc")
    c.check("reduced motion: an animation's page shows its still frame", src.endswith("-poster.png"),
            src)
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
      e.getBoundingClientRect().width > 0 && getComputedStyle(e).visibility !== 'hidden');
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
          .filter(a => !a.classList.contains('pilean-repo-link') &&
                       !a.classList.contains('pilean-page-link'))
          .map(a => a.getAttribute('href'))""")
        if mode == "site":
            c.check("site: no lean: link in a figure",
                    bool(hrefs) and not any(h.startswith("lean:") for h in hrefs), str(hrefs[:3]))
        if mode == "none":
            c.check("none: no link in a figure but the repository's and its page's", hrefs == [],
                    str(hrefs[:3]))
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


def shown_pictures(page):
    return page.evaluate("""() => [...document.querySelectorAll('figure.pilean-figure')].map(f => {
      const imgs = [...f.querySelectorAll('img')].filter(i => i.offsetParent !== null);
      return {id: f.id, motion: f.classList.contains('pilean-figure-has-motion'),
              shown: imgs.map(i => i.currentSrc || i.src),
              loaded: imgs.every(i => i.complete && i.naturalWidth > 0)};
    })""")


def anchor_space_checks(c, browser, base, label, urls):
    """The empty anchor at the start of a figure's page takes no space: the picture's top, within
    the page and below the page's title, is the same with the anchor as with it removed, at a
    wide and a narrow width."""
    measure = """() => {
      const p = document.querySelector('.pilean-figure-page');
      const pic = p.querySelector('.pilean-page-picture');
      const h1 = document.querySelector('main h1');
      return [pic.getBoundingClientRect().top - p.getBoundingClientRect().top,
              pic.getBoundingClientRect().top - (h1 ? h1.getBoundingClientRect().bottom : 0)]; }"""
    for width in [1440, 390]:
        ctx, page = new_page(browser, viewport={"width": width, "height": 900})
        for url in urls:
            goto(page, base + url)
            anchor = page.evaluate("""() => {
              const a = document.querySelector('.pilean-figure-page > .pilean-figure-page-anchor');
              if (!a) return null;
              const r = a.getBoundingClientRect();
              return [r.width, r.height, getComputedStyle(a).position]; }""")
            with_anchor = page.evaluate(measure)
            page.evaluate("document.querySelector('.pilean-figure-page-anchor').remove()")
            without = page.evaluate(measure)
            c.check(f"{label} {width} px: the anchor of {url} adds no space above the picture",
                    anchor is not None and anchor[:2] == [0, 0] and
                    all(abs(a - b) < 0.5 for a, b in zip(with_anchor, without)),
                    f"anchor {anchor}; with {with_anchor}, without {without}")
        ctx.close()


def option(args, name):
    return args[args.index(name) + 1] if name in args else None


def grid_column_checks(c, layouts):
    """The grids of stills follow the stills' widths: with motion off, the picture of two panels
    (720 px wide) has fewer columns than the small single motion (320 px), inline and on the
    figures' pages, at 1440 px, and never more at 768 px; at 390 px each has one column (two
    would show each still at less than three quarters of its width)."""
    two, small = "Example.twoFrames.svg", "Example.quarterTurn.svg"
    for where in ["inline", "page"]:
        a, b = layouts.get((two, where), {}), layouts.get((small, where), {})
        c.check(f"{where} at 1440 px: the two-panel picture's stills have fewer columns than the "
                "small motion's", 1440 in a and 1440 in b and a[1440] < b[1440],
                f"{a.get(1440)} and {b.get(1440)}")
        c.check(f"{where} at 768 px: the two-panel picture's stills have no more columns than the "
                "small motion's", 768 in a and 768 in b and a[768] <= b[768],
                f"{a.get(768)} and {b.get(768)}")
        c.check(f"{where} at 390 px: one still per row for both",
                a.get(390) == 1 and b.get(390) == 1, f"{a.get(390)} and {b.get(390)}")


def strict_grid_checks(c, browser, site):
    """Under a policy that allows the page's style elements by hash and no style attribute at all
    (`style-src-attr 'none'`), the grids of stills keep their widths: with motion off at 1440 px
    the two-panel picture's stills are one column and the small motion's more than one."""
    server, base = serve(site, styles="strict")
    ctx, page = new_page(browser, viewport={"width": 1440, "height": 900})
    goto(page, base + "Pictures-with-proofs/Motion/")
    page.evaluate("document.documentElement.setAttribute('data-motion', 'reduce')")
    page.wait_for_timeout(1000)
    # the number of the grid's columns, as the browser lays them out
    cols = page.evaluate("""() => Object.fromEntries([...document.querySelectorAll(
      '.pilean-motion-keys')].map(ol => [ol.closest('.pilean-motion').querySelector(
        'svg.pilean-motion-wide').getAttribute('data-pilean-file').split('/').pop(),
        getComputedStyle(ol).gridTemplateColumns.trim().split(/\\s+/).length]))""")
    # a style attribute of a figure (`width :=`) is refused under this policy, as it should be;
    # a refused style element of a figure (the grid's widths) would be the fault
    blocked = [r for r in figure_reports(page)
               if r["directive"].startswith("style-src-elem") and r["inFigure"]]
    two, small = cols.get("Example.twoFrames.svg"), cols.get("Example.quarterTurn.svg")
    c.check("without style-src-attr the grids keep their widths: the two-panel picture's stills "
            "one column at 1440 px, the small motion's more", two == 1 and (small or 0) > 1 and
            not blocked, f"{cols} {blocked[:2]}")
    ctx.close()
    server.shutdown()


def code_fold_checks(c, browser, base, shots):
    """A figure's page with more than 60 lines of code (the two-panel motion's) folds it in a
    closed `details` after its animation's section: the page is shorter than with it open, the
    summary is reached with Tab, has a ring of 3 px and opens it with Enter; a page with less code
    (the cubic plot's) shows it unfolded."""
    ctx, page = new_page(browser, viewport={"width": 1440, "height": 900})
    goto(page, base + "Figures/Example.twoFrames/")
    fold = page.locator("details.pilean-page-code-fold")
    order = page.evaluate("""() => { const a = document.querySelector('.pilean-page-motion'),
      k = document.querySelector('.pilean-page-codes');
      return !!(a && k && (a.compareDocumentPosition(k) & Node.DOCUMENT_POSITION_FOLLOWING)); }""")
    c.check("the two-panel motion's page folds its code, closed, after the animation",
            fold.count() == 1 and fold.get_attribute("open") is None and order,
            f"{fold.count()} {order}")
    closed = page.evaluate("document.documentElement.scrollHeight")
    if shots:
        page.screenshot(path=f"{shots}/code-fold-closed-1440.png", full_page=True)
    summary = fold.locator("summary")
    reached = False
    for _ in range(600):
        page.keyboard.press("Tab")
        if summary.evaluate("e => document.activeElement === e"):
            reached = True
            break
    ring = summary.evaluate("""e => { const s = getComputedStyle(e);
      return [s.outlineStyle, s.outlineWidth]; }""")
    c.check("the code's summary is a tab stop with a ring of 3 px",
            reached and ring == ["solid", "3px"], f"{reached} {ring}")
    page.keyboard.press("Enter")
    page.wait_for_timeout(200)
    opened = page.evaluate("document.documentElement.scrollHeight")
    c.check("Enter on the summary opens the code, which makes the page longer",
            fold.get_attribute("open") is not None and opened > closed + 200,
            f"{closed} -> {opened} px")
    goto(page, base + "Figures/Example.cubicPlot/")
    c.check("a page with less code shows it unfolded",
            page.locator("details.pilean-page-code-fold").count() == 0 and
            page.locator(".pilean-page-codes .pilean-page-decl").count() > 0)
    ctx.close()


def main(argv):
    site = argv[0]
    rest = argv[1:]
    shots = rest[0] if rest and not rest[0].startswith("--") else None
    sites = {"ideil": site, "site": option(rest, "--site-links"),
             "none": option(rest, "--no-links"), "side-by-side": option(rest, "--side-by-side")}
    manual = option(rest, "--manual")
    motions = option(rest, "--motions")
    workers = int(option(rest, "--workers") or "1")
    # Chromium only: some sections drive Chromium's DevTools protocol (event listeners, touch and
    # scroll gestures); `tools/site/motion_browser.py --engine` runs the motion checks elsewhere
    engine = "chromium"
    helpers = {"new_page": new_page, "goto": goto, "figure_reports": figure_reports,
               "layouts": {}, "listed": motion_browser.listed_motions(site), "engine": engine}
    server, base = serve(site)
    c = Checks()
    with sync_playwright() as p:
        browser = launch(p, engine)
        for scheme in ["light", "dark"]:
            ctx, page = new_page(browser, color_scheme=scheme,
                                 viewport={"width": 1100, "height": 900})
            for url in PAGES[:4]:
                goto(page, base + url)
                for fig in shown_pictures(page):
                    if fig["motion"]:
                        continue
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
                             r"verso/example/PictureExample/Figures\.lean#L\d+", repo) is not None, repo)
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
        c.check("the figures page lists twenty-two figures", items.count() == 22,
                str(items.count()))
        thumbs = page.evaluate("""() => [...document.querySelectorAll('.pilean-index-thumb img')]
            .every(i => i.complete && i.naturalWidth > 0)""")
        c.check("the figures page's pictures load", thumbs)
        files = page.locator(".pilean-index-files a").evaluate_all("as => as.map(a => a.href)")
        statuses = [ctx.request.get(h).status for h in files]
        c.check("every file the figures page links is served", all(s == 200 for s in statuses),
                str(statuses))
        manifest = page.locator(".pilean-figure-index-intro a").get_attribute("href")
        c.check("the manifest is linked and served",
                ctx.request.get(base + manifest).json()["format"] == "pilean-manifest-4")
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
                     noscript_checks, touch_checks, long_word_checks, figure_page_checks]:
            c.section(part.__name__, part, c, browser, base, shots)
        c.section("strict styles", strict_style_checks, c, browser, site)
        c.section("grid without style attributes", strict_grid_checks, c, browser, site)
        c.section("centring", centring_checks, c, browser, base, "stacked", [1100, 360],
                  FIGURE_PAGES)
        if sites["side-by-side"]:
            sbs_server, sbs_base = serve(sites["side-by-side"])
            c.section("column", column_checks, c, browser, sbs_base, shots)
            c.section("side-by-side centring", centring_checks, c, browser, sbs_base,
                      "side by side", [1400, 360], FIGURE_PAGES)
            sbs_server.shutdown()
        c.section("links", link_checks, c, browser, sites)
        c.section("freeze control", motion_browser.freeze_control, c, browser, engine)
        # every page with a motion: the two chapters' pages and the figures' pages
        motion_browser.motion_pages_checks(
            c, browser, base, [(url, f"blueprint {url}",
                                4 if url == "Pictures-with-proofs/Motion/" else 1)
                               for url in motion_browser.motion_pages(site)],
            helpers, motions, shots, workers)
        c.section("grid columns", grid_column_checks, c, helpers["layouts"])
        c.section("code fold", code_fold_checks, c, browser, base, shots)
        c.section("anchor space", anchor_space_checks, c, browser, base, "blueprint",
                  ["Figures/Example.cubicPlot/", "Figures/Example.sketch/",
                   "Figures/Example.radiusExplorer/"])
        if manual:
            manual_server, manual_base = serve(manual)
            c.section("manual anchor space", anchor_space_checks, c, browser, manual_base,
                      "manual", ["Figures/ManualExample.trianglePlot/",
                                 "Figures/ManualExample.radiusSlider/"])
            manual_helpers = dict(helpers, listed=motion_browser.listed_motions(manual),
                                  layouts={})
            motion_browser.motion_pages_checks(
                c, browser, manual_base, [(url, f"manual {url}", 2 if url == "Motion/" else 1)
                                          for url in motion_browser.motion_pages(manual)],
                manual_helpers, motions, shots, workers)
            manual_server.shutdown()

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
