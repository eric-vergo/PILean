# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
"""What a page loaded by `runner.swift` cannot do (macOS only):

    python3 tools/webkit/runner_test.py [--runner PATH]

A page in a temporary folder tries to reach a local HTTP server (an image, a script, `fetch`, a
beacon, then `location` set to the server), to post a message to the program (the bridge an
earlier runner had), and to load a file outside its folder. Each must fail: the server must see
no request, no file may be written, the page must still be there when the script returns, and
the runner must refuse a URL that is not a file below its folder. Exit status 0 when all hold.
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

PAGE = """<!doctype html><html><head><meta charset="utf-8"><title>probe</title></head><body>
<p id="here">here</p>
<img src="http://127.0.0.1:{port}/img.png">
<script src="http://127.0.0.1:{port}/script.js"></script>
<iframe src="file://{outside}"></iframe>
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
try { const r = await fetch('file://' + OUTSIDE); tried.outside = 'read ' + (await r.text()); }
catch (e) { tried.outside = 'refused: ' + e.name; }
location.href = 'http://127.0.0.1:' + PORT + '/navigate';
await new Promise(r => setTimeout(r, 1500));
tried.still = document.getElementById('here') ? 'here' : 'gone';
tried.at = location.href;
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
    outside = os.path.join(work, "outside.txt")
    with open(outside, "w") as f:
        f.write("outside")
    shot = os.path.join(work, "shot.png")
    page = os.path.join(root, "page.html")
    with open(page, "w") as f:
        f.write(PAGE.format(port=port, outside=outside))
    script = os.path.join(work, "script.js")
    with open(script, "w") as f:
        f.write(f"const PORT = {port}; const SHOT = {json.dumps(shot)}; "
                f"const OUTSIDE = {json.dumps(outside)};\n" + SCRIPT)
    ok = True
    try:
        out = webkit_check.run_page(runner, root, page, script, 400, 300, 20)
        tried = json.loads(out) if out.startswith("{") else {}
        holds = (bool(tried) and tried.get("post", "").startswith("no bridge") and
                 tried.get("fetch", "").startswith("refused") and tried.get("beacon") is not True
                 and not tried.get("outside", "").startswith("read") and
                 tried.get("still") == "here" and not seen and not os.path.exists(shot))
        ok = ok and holds
        print(f"the page's attempts: {tried or out}; requests the server saw: {seen}; a file "
              f"written: {os.path.exists(shot)} -> {'ok' if holds else 'FAILED'}")
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
