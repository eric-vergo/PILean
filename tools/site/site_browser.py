# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
"""What PILean's browser checks of a site share (`tools/site/`): a server for the built site
(`serve`) that sends a strict content policy with every page (scripts only from the site's files
and the inline scripts of the head, by hash; no inline event handlers; styles inline, or with
`styles="hashes"` the style elements by hash only; nothing from elsewhere), new pages that record
the policy's reports, the changes of live regions and the alerts (`new_page`), the reports about
figures (`figure_reports`), and the tally of checks (`Checks`). Needs the `playwright` package and
a Chromium it can find.
"""

import base64
import functools
import hashlib
import http.server
import re
import threading

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
    inFigure: !!(t && t.closest('.pilean-figure, .pilean-figure-list, .pilean-figure-page'))});
});
"""

TIMEOUT = 10000

# The engines Playwright drives here. Chromium is the one the checks are measured on and the one
# a continuous-integration gate uses; Firefox runs the same checks, but for those that rest on an
# observation of Chromium (said where they are).
ENGINES = ("chromium", "firefox")


def engine_option(args, default="chromium"):
    """The value of `--engine NAME` in `args` (removed from it), or `default`."""
    if "--engine" not in args:
        return default
    i = args.index("--engine")
    name = args[i + 1]
    del args[i:i + 2]
    return name


def launch(p, engine="chromium"):
    """A headless browser of the engine `engine` (one of `ENGINES`) from Playwright `p`."""
    if engine not in ENGINES:
        raise ValueError(f"unknown engine {engine}: one of {', '.join(ENGINES)}")
    return getattr(p, engine).launch()


def new_page(browser, **kw):
    ctx = browser.new_context(**kw)
    ctx.add_init_script(REPORTS)
    ctx.set_default_timeout(TIMEOUT)
    return ctx, ctx.new_page()


def goto(page, url):
    page.goto(url)
    page.wait_for_load_state("networkidle")


class Checks:
    """Counts checks and prints each verdict, or keeps the lines in `lines` when `keep` is set
    (for a worker process whose lines are printed by its parent)."""

    def __init__(self, keep=False):
        self.failed = 0
        self.count = 0
        self.lines = [] if keep else None

    def say(self, line):
        if self.lines is None:
            print(line, flush=True)
        else:
            self.lines.append(line)

    def section(self, name, fn, *args):
        """Runs a group of checks, and says how long it took; one that stops with an error counts
        as a failure."""
        import time
        start = time.monotonic()
        try:
            fn(*args)
        except Exception as e:  # noqa: BLE001 - a check that cannot run is a failed check
            import traceback
            where = traceback.extract_tb(e.__traceback__)[-1]
            self.check(f"{name} ran to its end", False,
                       f"{str(e).splitlines()[0]} (line {where.lineno})")
        self.say(f"time: {name}: {time.monotonic() - start:.1f} s")

    def check(self, name, ok, detail=""):
        self.count += 1
        if ok:
            self.say(f"ok: {name}")
        else:
            self.failed += 1
            self.say(f"FAIL: {name} {detail}")
