# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
"""Checks the example site's figures in a headless Chromium (Playwright).

    python3 browser_check.py SITE [SHOTS]

SITE is the generator's `html-multi` folder, built with `--figure-repo`; SHOTS, if given, is a
folder for screenshots. The site is served on 127.0.0.1 with a strict content policy: scripts only
from the site's files and the inline scripts of the head (by hash), no inline event handlers, no
plug-ins, nothing from elsewhere. Checked: every picture loads in the light and the dark theme and
the right one is shown; the source line's links; the figures page; the still frame under reduced
motion; no horizontal scrolling at narrow widths; no content-policy report about a figure. For the
explorers: the slider and the stepper change the frame (by pointer and by keyboard), the view
zooms and resets from the keyboard, an inline element links to its declaration and carries its
title, the inline tint follows the theme, without script every frame is listed, reduced motion
has no play button, and at 360 px the narrow rendition is shown.
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


def policy(page: bytes) -> str:
    head = page.split(b"</head>", 1)[0]
    hashes = [
        "'sha256-" + base64.b64encode(hashlib.sha256(m).digest()).decode() + "'"
        for m in HEAD_SCRIPT.findall(head)
    ]
    scripts = " ".join(["'self'", "'wasm-unsafe-eval'"] + hashes)
    return (
        f"default-src 'self'; script-src {scripts}; script-src-attr 'none'; "
        "style-src 'self' 'unsafe-inline'; object-src 'none'; base-uri 'self'; "
        "form-action 'none'; frame-src 'none'; frame-ancestors 'none'"
    )


class Handler(http.server.SimpleHTTPRequestHandler):
    def log_message(self, *args):
        pass

    def end_headers(self):
        path = self.translate_path(self.path)
        if path.endswith("/"):
            path += "index.html"
        if path.endswith(".html"):
            try:
                with open(path, "rb") as f:
                    self.send_header("Content-Security-Policy", policy(f.read()))
            except OSError:
                pass
        super().end_headers()


# Verso's v4.35.0-patch1 release loads its docstring Markdown renderer from jsDelivr (the owner's
# Verso fork ships it with the site); the strict policy blocks it. That report is about Verso's page,
# not about a figure, and is left out of the checks below.
VERSO_CDN = "https://cdn.jsdelivr.net/npm/marked@"


def figure_reports(page):
    return [r for r in page.evaluate("window.__cspReports")
            if r["directive"] != "script-src-attr"
            and not (r["blocked"] or "").startswith(VERSO_CDN)]


REPORTS = """
window.__cspReports = [];
document.addEventListener('securitypolicyviolation', e => {
  window.__cspReports.push({directive: e.effectiveDirective, blocked: e.blockedURI,
    sample: e.sample, source: e.sourceFile});
});
"""

PAGES = ["Pictures-with-proofs/A-function/", "Pictures-with-proofs/Data/",
         "Pictures-with-proofs/A-relation/", "Pictures-with-proofs/Motion/", "Figures/",
         "Pictures-with-proofs/Explorers/"]
EXPLORERS = "Pictures-with-proofs/Explorers/"


def current(page, fig):
    return page.evaluate(f"""() => {{
      const f = document.querySelector('figure#{fig}');
      const shown = [...f.querySelectorAll('li.pilean-explorer-frame')]
        .filter(li => li.offsetParent !== null);
      return shown.map(li => Number(li.dataset.index));
    }}""")


def explorer_checks(c, browser, base, shots):
    """The explorers and the inline figure (see the module docstring)."""
    for scheme in ["light", "dark"]:
        ctx = browser.new_context(color_scheme=scheme, viewport={"width": 1100, "height": 900})
        ctx.add_init_script(REPORTS)
        page = ctx.new_page()
        page.goto(base + EXPLORERS)
        page.wait_for_load_state("networkidle")
        fill = page.evaluate("""() => getComputedStyle(document.querySelector(
          'figure#inline svg path[fill-opacity]')).fill""")
        c.check(f"{scheme}: the inline picture's tint follows the theme",
                ("rgb(0, 104, 166)" == fill) == (scheme == "light"), fill)
        reports = figure_reports(page)
        c.check(f"{scheme}: the explorers page has no content-policy report", not reports,
                str(reports))
        if shots:
            page.screenshot(path=f"{shots}/{scheme}-explorers.png", full_page=True)
        ctx.close()

    ctx = browser.new_context(viewport={"width": 1100, "height": 900})
    ctx.add_init_script(REPORTS)
    page = ctx.new_page()
    page.goto(base + EXPLORERS)
    page.wait_for_load_state("networkidle")
    c.check("the slider shows the poster frame only", current(page, "radius") == [2],
            str(current(page, "radius")))
    page.evaluate("""() => { const s = document.querySelector('figure#radius input[type=range]');
      s.value = '4'; s.dispatchEvent(new Event('input', {bubbles: true})); }""")
    c.check("moving the slider changes the frame", current(page, "radius") == [4],
            str(current(page, "radius")))
    out = page.locator("figure#radius .pilean-explorer-value").inner_text()
    c.check("the slider's value is announced", out == "10/10", out)
    page.locator("figure#radius input[type=range]").focus()
    page.keyboard.press("ArrowLeft")
    c.check("the slider works from the keyboard", current(page, "radius") == [3],
            str(current(page, "radius")))
    page.locator("figure#word [data-action=next]").click()
    counter = page.locator("figure#word .pilean-explorer-counter").inner_text()
    c.check("next shows the second step", current(page, "word") == [1] and counter == "Step 2 of 4",
            counter)
    page.locator("figure#word [data-action=prev]").click()
    c.check("previous shows the first step again", current(page, "word") == [0])
    page.locator("figure#word [data-action=next]").focus()
    page.keyboard.press("Enter")
    caption = page.locator("figure#word .pilean-explorer-caption").inner_text()
    c.check("the stepper works from the keyboard, its caption announced",
            current(page, "word") == [1] and caption.startswith("a:"), caption)
    view = page.locator("figure#radius .pilean-explorer-view")
    box0 = page.evaluate("""() => document.querySelector(
      'figure#radius li.pilean-explorer-current svg').getAttribute('viewBox')""")
    view.focus()
    page.keyboard.press("+")
    box1 = page.evaluate("""() => document.querySelector(
      'figure#radius li.pilean-explorer-current svg').getAttribute('viewBox')""")
    page.keyboard.press("0")
    box2 = page.evaluate("""() => document.querySelector(
      'figure#radius li.pilean-explorer-current svg').getAttribute('viewBox')""")
    c.check("+ zooms the view and 0 resets it",
            float(box1.split()[2]) < float(box0.split()[2]) and box2.split()[2] == box0.split()[2],
            f"{box0} / {box1} / {box2}")
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
    ctx.close()

    ctx = browser.new_context(java_script_enabled=False, viewport={"width": 1100, "height": 900})
    page = ctx.new_page()
    page.goto(base + EXPLORERS)
    shown = current(page, "radius")
    hidden = page.locator("figure#radius .pilean-explorer-controls").is_hidden()
    c.check("without script every frame is shown and the controls are hidden",
            shown == [0, 1, 2, 3, 4] and hidden, str(shown))
    ctx.close()

    ctx = browser.new_context(reduced_motion="reduce")
    page = ctx.new_page()
    page.goto(base + EXPLORERS)
    page.wait_for_load_state("networkidle")
    c.check("reduced motion: no play button",
            page.locator("figure#word [data-action=play]").is_hidden())
    ctx.close()

    ctx = browser.new_context(viewport={"width": 360, "height": 800})
    page = ctx.new_page()
    page.goto(base + EXPLORERS)
    page.wait_for_load_state("networkidle")
    narrow = page.evaluate("""() => [...document.querySelectorAll('figure#inline svg')]
      .filter(s => s.getBoundingClientRect().width > 0).map(s => s.id)""")
    c.check("360 px: the inline figure shows its narrow rendition",
            narrow == ["inline-svg-narrow"], str(narrow))
    ctx.close()


class Checks:
    def __init__(self):
        self.failed = 0
        self.count = 0

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


def main(site, shots=None):
    handler = functools.partial(Handler, directory=site)
    server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), handler)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    base = f"http://127.0.0.1:{server.server_address[1]}/"
    c = Checks()
    with sync_playwright() as p:
        browser = p.chromium.launch()
        for scheme in ["light", "dark"]:
            ctx = browser.new_context(color_scheme=scheme, viewport={"width": 1100, "height": 900})
            ctx.add_init_script(REPORTS)
            page = ctx.new_page()
            for url in PAGES[:4]:
                page.goto(base + url)
                page.wait_for_load_state("networkidle")
                for fig in shown_pictures(page):
                    c.check(f"{scheme}: {fig['id']} shows one picture, loaded",
                            len(fig["shown"]) == 1 and fig["loaded"], str(fig))
                    if fig["id"] != "circle" and fig["shown"]:
                        dark = fig["shown"][0].endswith("-dark.svg")
                        c.check(f"{scheme}: {fig['id']} follows the system's scheme",
                                dark == (scheme == "dark"), fig["shown"][0])
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

        ctx = browser.new_context(viewport={"width": 1100, "height": 900})
        page = ctx.new_page()
        page.goto(base + PAGES[0])
        fig = page.locator("figure#cubic")
        c.check("the figure has its number", "Figure 1.1.1" in fig.inner_text())
        lean_link = fig.locator(".pilean-figure-source a.pilean-lean-link").first
        text = fig.locator(".pilean-figure-source code.pilean-lean-text").first
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
        c.check("the figures page lists seven figures", items.count() == 7)
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
            page.goto(base + "Pictures-with-proofs/Motion/")
            page.wait_for_load_state("networkidle")
            src = page.locator("figure#circle img").evaluate("i => i.currentSrc")
            c.check(f"reduced motion {motion}: the animation shows {expect}", src.endswith(expect),
                    src)
            ctx.close()

        explorer_checks(c, browser, base, shots)

        for width in [320, 360, 375, 600]:
            ctx = browser.new_context(viewport={"width": width, "height": 800})
            page = ctx.new_page()
            for url in PAGES:
                page.goto(base + url)
                page.wait_for_load_state("networkidle")
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
    sys.exit(main(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else None))
