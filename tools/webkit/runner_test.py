# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
"""What a page loaded by `runner.swift` cannot do (macOS only):

    python3 tools/webkit/runner_test.py [--runner PATH]

A page in a folder of its own tries to reach a local HTTP server (an image, a script, `fetch`, a
beacon, then `location` set to the server), to post a message to the program through
`window.webkit.messageHandlers`, and to load an image and a stylesheet from outside its folder,
each spelt four ways (an absolute `file:` URL, `../`, `%2e%2e/` and a `localhost` host). Each must
fail: the server sees no request, no file is written, no outside image has a size and no outside
style applies, and the page is still there when the script returns; an image and a stylesheet
inside the folder must load, so that the test is not passed by a page that loads nothing. The
runner must also refuse a URL that is not a file below its folder. Exit status 0 when all hold.
"""

import http.server
import json
import os
import shutil
import subprocess
import sys
import tempfile
import threading

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import webkit_check  # noqa: E402

# a 1 by 1 PNG
PNG = bytes.fromhex("89504e470d0a1a0a0000000d4948445200000001000000010806000000"
                    "1f15c4890000000d4944415478da63f8ffff3f0005fe02fea7d605d6"
                    "0000000049454e44ae426082")

# the four spellings of a file outside the page's folder, from the folder `root` in `work`
SPELLINGS = ["file://{work}/{name}", "../{name}", "%2e%2e/{name}", "file://localhost{work}/{name}"]

PAGE = """<!doctype html><html><head><meta charset="utf-8"><title>probe</title>
<link rel="stylesheet" href="inside.css">
{links}
</head><body>
<p id="here">here</p><p id="in">in</p>{marks}
<img id="img-in" src="inside.png">{imgs}
<img src="http://127.0.0.1:{port}/img.png">
<script src="http://127.0.0.1:{port}/script.js"></script>
</body></html>
"""

SCRIPT = """
const tried = {};
try {
  window.webkit.messageHandlers.ctl.postMessage('shot:' + SHOT);
  tried.post = 'posted';
} catch (e) { tried.post = 'no bridge: ' + e.name; }
try { await fetch('http://127.0.0.1:' + PORT + '/fetch'); tried.fetch = 'fetched'; }
catch (e) { tried.fetch = 'refused: ' + e.name; }
try { tried.beacon = navigator.sendBeacon('http://127.0.0.1:' + PORT + '/beacon', 'x'); }
catch (e) { tried.beacon = 'refused: ' + e.name; }
await new Promise(r => setTimeout(r, 800));
const size = id => document.getElementById(id).naturalWidth;
const colour = id => getComputedStyle(document.getElementById(id)).color;
tried.inside = [size('img-in'), colour('in')];
tried.outside = [0, 1, 2, 3].map(k => [size('img-' + k), colour('m' + k)]);
location.href = 'http://127.0.0.1:' + PORT + '/navigate';
await new Promise(r => setTimeout(r, 1500));
tried.still = document.getElementById('here') ? 'here' : 'gone';
return JSON.stringify(tried);
"""


def main(argv):
    if sys.platform != "darwin":
        print("runner_test: macOS only; nothing checked")
        return 2
    runner = argv[argv.index("--runner") + 1] if "--runner" in argv else \
        webkit_check.build_runner()
    seen = []

    class Count(http.server.BaseHTTPRequestHandler):
        def do_GET(self):  # noqa: N802 - the name http.server calls
            seen.append(self.path)
            self.send_response(200)
            self.end_headers()

        do_POST = do_GET  # noqa: N815

        def log_message(self, *args):
            pass

    server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Count)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    port = server.server_address[1]
    work = tempfile.mkdtemp(prefix="pilean-runner-test-")
    root = os.path.join(work, "root")
    os.makedirs(root)
    with open(os.path.join(root, "inside.png"), "wb") as f:
        f.write(PNG)
    with open(os.path.join(root, "inside.css"), "w") as f:
        f.write("#in { color: rgb(4, 5, 6); }")
    links, marks, imgs = [], [], []
    for k, spelling in enumerate(SPELLINGS):
        with open(os.path.join(work, f"outside-{k}.png"), "wb") as f:
            f.write(PNG)
        with open(os.path.join(work, f"outside-{k}.css"), "w") as f:
            f.write(f"#m{k} {{ color: rgb(1, 2, {k + 3}); }}")
        css = spelling.format(work=work, name=f"outside-{k}.css")
        png = spelling.format(work=work, name=f"outside-{k}.png")
        links.append(f'<link rel="stylesheet" href="{css}">')
        marks.append(f'<p id="m{k}">m{k}</p>')
        imgs.append(f'<img id="img-{k}" src="{png}">')
    outside = os.path.join(work, "outside-0.png")
    shot = os.path.join(work, "shot.png")
    page = os.path.join(root, "page.html")
    with open(page, "w") as f:
        f.write(PAGE.format(port=port, links="\n".join(links), marks="".join(marks),
                            imgs="".join(imgs)))
    script = os.path.join(work, "script.js")
    with open(script, "w") as f:
        f.write(f"const PORT = {port}; const SHOT = {json.dumps(shot)};\n" + SCRIPT)
    ok = True
    try:
        out = webkit_check.run_page(runner, root, page, script, 400, 300, 20)
        tried = json.loads(out) if out.startswith("{") else {}
        inside_ok = tried.get("inside") == [1, "rgb(4, 5, 6)"]
        outside_ok = bool(tried.get("outside")) and all(
            w == 0 and c == "rgb(0, 0, 0)" for w, c in tried["outside"])
        holds = (bool(tried) and tried.get("post", "").startswith("no bridge") and
                 tried.get("fetch", "").startswith("refused") and tried.get("beacon") is not True
                 and tried.get("still") == "here" and inside_ok and outside_ok and not seen and
                 not os.path.exists(shot))
        ok = ok and holds
        print(f"the page's attempts: {tried or out}; inside the folder the image and the style "
              f"load: {inside_ok}; outside, in four spellings, neither does: {outside_ok}; "
              f"requests the server saw: {seen}; a file written: {os.path.exists(shot)} -> "
              f"{'ok' if holds else 'FAILED'}")
        for url in [f"http://127.0.0.1:{port}/", "file://" + outside]:
            r = subprocess.run([runner, root, url, script], capture_output=True, text=True,
                               timeout=30)
            holds = r.returncode == 2 and not r.stdout.strip()
            ok = ok and holds
            print(f"the runner asked for {url}: exit {r.returncode}, "
                  f"{(r.stderr.strip() or r.stdout.strip())[:80]} -> {'ok' if holds else 'FAILED'}")
        holds = not seen
        ok = ok and holds
        print(f"requests the server saw in all: {seen} -> {'ok' if holds else 'FAILED'}")
    finally:
        server.shutdown()
        shutil.rmtree(work, ignore_errors=True)
    print(f"runner_test: {'all hold' if ok else 'FAILED'}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
