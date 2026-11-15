# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
"""Checks the example site's figures in a headless Chromium (Playwright).

    python3 browser_check.py SITE [SHOTS]

SITE is the generator's `html-multi` folder, built with `--figure-repo`; SHOTS, if given, is a
folder for screenshots. The site is served on 127.0.0.1 with a strict content policy: scripts only
from the site's files and the inline scripts of the head (by hash), no inline event handlers, no
plug-ins, nothing from elsewhere. Checked: every picture loads in the light and the dark theme and
the right one is shown; the source line's links; the figures page; the still frame under reduced
motion; no horizontal scrolling at narrow widths; no content-policy report about a figure.
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


REPORTS = """
window.__cspReports = [];
document.addEventListener('securitypolicyviolation', e => {
  window.__cspReports.push({directive: e.effectiveDirective, blocked: e.blockedURI,
    sample: e.sample, source: e.sourceFile});
});
"""

PAGES = ["Pictures-with-proofs/A-function/", "Pictures-with-proofs/Data/",
         "Pictures-with-proofs/A-relation/", "Pictures-with-proofs/Motion/", "Figures/"]


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
                reports = [r for r in page.evaluate("window.__cspReports")
                           if r["directive"] != "script-src-attr"]
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
        c.check("the figures page lists four figures", items.count() == 4)
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

        for width in [320, 375, 600]:
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
