// Released under Apache 2.0 license as described in the file LICENSE.
// Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
//
// Loads one page in the system's WebKit (a `WKWebView`, the engine of Safari) and runs a script in
// it: the body of an async JavaScript function, whose result (a string) is printed on stdout.
// macOS only; it uses the frameworks of the system and nothing else.
//
//   runner URL SCRIPT [WIDTH HEIGHT]
//
// The page lives in a window, because WebKit does not run the clock of an SVG animation in a view
// that is in no window, or in a window outside every screen: the clock stays at 0. The window is
// what the desktop sees of this program, and all of it:
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
// The program never moves the pointer, never sends events, and reads nothing but the URL and the
// script. A message `shot:PATH` posted to `window.webkit.messageHandlers.ctl` saves a picture of
// the page as a PNG at PATH.
import AppKit
import WebKit

/// The window that holds the page, kept for the pictures the script asks for.
var window: NSWindow? = nil

/// Receives the script's messages: `shot:PATH` saves a picture of the page.
final class Control: NSObject, WKScriptMessageHandler {
  func userContentController(_ controller: WKUserContentController,
                             didReceive message: WKScriptMessage) {
    let body = (message.body as? String) ?? ""
    guard body.hasPrefix("shot:"), let web = window?.contentView as? WKWebView else { return }
    let path = String(body.dropFirst(5))
    web.takeSnapshot(with: nil) { image, _ in
      guard let image = image, let tiff = image.tiffRepresentation,
            let bitmap = NSBitmapImageRep(data: tiff),
            let png = bitmap.representation(using: .png, properties: [:]) else { return }
      try? png.write(to: URL(fileURLWithPath: path))
    }
  }
}

/// Loads the page and, once it has loaded, runs the script and exits with its result.
final class Runner: NSObject, WKNavigationDelegate {
  let web: WKWebView
  let script: String

  init(url: URL, script: String, width: Double, height: Double) {
    let config = WKWebViewConfiguration()
    config.userContentController.add(Control(), name: "ctl")
    web = WKWebView(frame: NSRect(x: 0, y: 0, width: width, height: height), configuration: config)
    self.script = script
    super.init()
    web.navigationDelegate = self
    if url.isFileURL {
      web.loadFileURL(url, allowingReadAccessTo: url.deletingLastPathComponent())
    } else {
      web.load(URLRequest(url: url))
    }
  }

  func webView(_ webView: WKWebView, didFinish navigation: WKNavigation!) {
    web.callAsyncJavaScript(script, arguments: [:], in: nil, in: .page) { result in
      switch result {
      case .success(let value): print((value as? String) ?? String(describing: value))
      case .failure(let error): print("ERROR script: \(error)")
      }
      exit(0)
    }
  }

  func webView(_ webView: WKWebView, didFail navigation: WKNavigation!, withError error: Error) {
    print("ERROR navigation: \(error)")
    exit(1)
  }

  func webView(_ webView: WKWebView, didFailProvisionalNavigation navigation: WKNavigation!,
               withError error: Error) {
    print("ERROR navigation: \(error)")
    exit(1)
  }
}

let args = CommandLine.arguments
guard args.count == 3 || args.count == 5, let url = URL(string: args[1]),
      let script = try? String(contentsOfFile: args[2], encoding: .utf8) else {
  FileHandle.standardError.write("usage: runner URL SCRIPT [WIDTH HEIGHT]\n".data(using: .utf8)!)
  exit(2)
}
let width = args.count == 5 ? Double(args[3]) ?? 1280 : 1280
let height = args.count == 5 ? Double(args[4]) ?? 800 : 800

let app = NSApplication.shared
app.setActivationPolicy(.accessory)
let runner = Runner(url: url, script: script, width: width, height: height)
let win = NSWindow(contentRect: NSRect(x: 0, y: 0, width: width, height: height),
                   styleMask: [.borderless], backing: .buffered, defer: false)
win.alphaValue = 0
win.isOpaque = false
win.hasShadow = false
win.ignoresMouseEvents = true
win.isExcludedFromWindowsMenu = true
win.collectionBehavior = [.transient, .ignoresCycle]
win.contentView = runner.web
win.orderFrontRegardless()
window = win

let limit = Double(ProcessInfo.processInfo.environment["WEBKIT_TIMEOUT"] ?? "") ?? 120
DispatchQueue.main.asyncAfter(deadline: .now() + limit) {
  print("ERROR timeout after \(limit) s")
  exit(3)
}
app.run()
