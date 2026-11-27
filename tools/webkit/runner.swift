// Released under Apache 2.0 license as described in the file LICENSE.
// Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
//
// Loads one local page in the system's WebKit (a `WKWebView`, the engine of Safari) and runs a
// script in it: the body of an async JavaScript function, whose result (a string) is printed on
// stdout. macOS only; it uses the frameworks of the system and nothing else.
//
//   runner ROOT URL SCRIPT [WIDTH HEIGHT]
//
// What the page may do. URL must be a `file:` URL of a file below the folder ROOT. Every
// navigation (of the page or of a frame: a link, a redirect, a script setting `location`) to
// anything but a file below ROOT is refused, and a content rule list blocks every load whose URL
// is not a `file:` URL (scripts, images, styles, frames, `fetch`, XHR, beacons, WebSockets), so the
// page reaches no network. Files are readable below ROOT only. There is no bridge from the page to
// this program: no message handler, nothing the page can call; the program only reads the value
// the script returns.
//
// What the desktop sees. The page lives in a window, because WebKit does not run the clock of an
// SVG animation in a view that is in no window, or in a window outside every screen (the clock
// stays at 0). The window is:
//
//   * borderless, fully transparent (alpha 0) and click-through (it ignores the mouse), so nothing
//     shows and every click goes to the window below;
//   * put in front of the other windows without activating the program: the program is an
//     accessory (no Dock icon, no menu bar), a borderless window never becomes the key window, so
//     the focus and the keyboard stay where they are;
//   * left out of the window cycle and of Exposé, without a shadow;
//   * closed when the program exits: after the script returns, or after `WEBKIT_TIMEOUT` seconds
//     (120 by default).
//
// The program never moves the pointer and never sends events. Its website data are not kept
// (`WKWebsiteDataStore.nonPersistent`), its compiled content rules go to the temporary directory,
// and `webkit_check.py` runs it with `CFFIXED_USER_HOME` set to a temporary folder, so that what
// WebKit keeps for any program (caches, a data folder) is written there and removed, never into
// the user's Library.
import AppKit
import WebKit

/// Every load whose URL is not a `file:` URL is blocked.
let rules = """
  [{"trigger": {"url-filter": ".*"}, "action": {"type": "block"}},
   {"trigger": {"url-filter": "^file:"}, "action": {"type": "ignore-previous-rules"}}]
  """

/// Whether `url` is a `file:` URL of a file below the folder `root`.
func isBelow(_ url: URL, _ root: URL) -> Bool {
  guard url.isFileURL else { return false }
  let path = url.standardizedFileURL.resolvingSymlinksInPath().path
  let base = root.standardizedFileURL.resolvingSymlinksInPath().path
  return path == base || path.hasPrefix(base.hasSuffix("/") ? base : base + "/")
}

/// Prints `message` on stderr.
func warn(_ message: String) {
  FileHandle.standardError.write((message + "\n").data(using: .utf8)!)
}

/// Loads the page and, once it has loaded, runs the script and exits with its result.
final class Runner: NSObject, WKNavigationDelegate {
  let web: WKWebView
  let script: String
  let root: URL
  var ran = false

  init(root: URL, script: String, width: Double, height: Double, rules: WKContentRuleList) {
    let config = WKWebViewConfiguration()
    config.userContentController.add(rules)
    config.websiteDataStore = .nonPersistent()
    web = WKWebView(frame: NSRect(x: 0, y: 0, width: width, height: height), configuration: config)
    self.script = script
    self.root = root
    super.init()
    web.navigationDelegate = self
  }

  func load(_ url: URL) {
    web.loadFileURL(url, allowingReadAccessTo: root)
  }

  func webView(_ webView: WKWebView, decidePolicyFor action: WKNavigationAction,
               decisionHandler: @escaping (WKNavigationActionPolicy) -> Void) {
    if let url = action.request.url, isBelow(url, root) {
      decisionHandler(.allow)
    } else {
      warn("runner: refused to load \(action.request.url?.absoluteString ?? "?")")
      decisionHandler(.cancel)
    }
  }

  func webView(_ webView: WKWebView, didFinish navigation: WKNavigation!) {
    if ran { return }
    ran = true
    web.callAsyncJavaScript(script, arguments: [:], in: nil, in: .page) { result in
      switch result {
      case .success(let value): print((value as? String) ?? String(describing: value))
      case .failure(let error): print("ERROR script: \(error)")
      }
      exit(0)
    }
  }

  func webView(_ webView: WKWebView, didFail navigation: WKNavigation!, withError error: Error) {
    if ran { return }
    print("ERROR navigation: \(error)")
    exit(1)
  }

  func webView(_ webView: WKWebView, didFailProvisionalNavigation navigation: WKNavigation!,
               withError error: Error) {
    if ran { return }
    print("ERROR navigation: \(error)")
    exit(1)
  }
}

let args = CommandLine.arguments
guard args.count == 4 || args.count == 6,
      let script = try? String(contentsOfFile: args[3], encoding: .utf8) else {
  warn("usage: runner ROOT URL SCRIPT [WIDTH HEIGHT]")
  exit(2)
}
let root = URL(fileURLWithPath: args[1], isDirectory: true)
guard let url = URL(string: args[2]), isBelow(url, root) else {
  warn("runner: URL must be a file: URL of a file below ROOT")
  exit(2)
}
let width = args.count == 6 ? Double(args[4]) ?? 1280 : 1280
let height = args.count == 6 ? Double(args[5]) ?? 800 : 800

let app = NSApplication.shared
app.setActivationPolicy(.accessory)
var runner: Runner? = nil
// The compiled rule list goes to a folder of the temporary directory, not to the user's Library.
let ruleStore = URL(fileURLWithPath: NSTemporaryDirectory(), isDirectory: true)
  .appendingPathComponent("pilean-runner-rules-\(getpid())", isDirectory: true)
guard let store = WKContentRuleListStore(url: ruleStore) else {
  warn("runner: no store for the content rules")
  exit(1)
}
atexit { try? FileManager.default.removeItem(at: ruleStore) }
store.compileContentRuleList(
  forIdentifier: "pilean-runner-local-only", encodedContentRuleList: rules) { list, error in
  guard let list = list else {
    print("ERROR rules: \(String(describing: error))")
    exit(1)
  }
  let r = Runner(root: root, script: script, width: width, height: height, rules: list)
  let win = NSWindow(contentRect: NSRect(x: 0, y: 0, width: width, height: height),
                     styleMask: [.borderless], backing: .buffered, defer: false)
  win.alphaValue = 0
  win.isOpaque = false
  win.hasShadow = false
  win.ignoresMouseEvents = true
  win.isExcludedFromWindowsMenu = true
  win.collectionBehavior = [.transient, .ignoresCycle]
  win.contentView = r.web
  win.orderFrontRegardless()
  runner = r
  r.load(url)
}

let limit = Double(ProcessInfo.processInfo.environment["WEBKIT_TIMEOUT"] ?? "") ?? 120
DispatchQueue.main.asyncAfter(deadline: .now() + limit) {
  print("ERROR timeout after \(limit) s")
  exit(3)
}
app.run()
