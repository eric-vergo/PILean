/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Trust.Figure

/-!
# Inline pictures and explorers

A page can put a figure's picture inline, as an `svg` element of the page, instead of an `img` of
its file (`:::figure … (inline := true)`, and every frame of `:::figure_explorer`). Inline, the
elements that carry metadata are part of the page: a `title` gives the browser's hover text, and an
element with a `data-lean-decl` becomes a link to its declaration when the site's link mode gives
it one (`PILeanVerso.LeanLinks`), with a visible focus ring. A link is never put inside another.

* **Ids.** Every `id` of a picture, every `url(#…)` and `#…` reference to one, and every
  `data-pilean-actor` (the moving items of a motion) gets a prefix unique in the page
  (`prefixNode`), so that several pictures can share a page. The picture's own id is made of ASCII
  letters, digits, `-` and `_` only (`domSafe`).
* **Themes.** One inline picture serves both themes: a `style` element inside it (class
  `pilean-theme`) restyles its light colours to its dark twin's (`InlineSvg.darkColours`,
  `darkOpacities`) under the page's `data-theme="dark"`, or the system's dark scheme when the page
  does not say `light` (the selectors the `-dark` files use). Rules match the presentation
  attributes the writer emits (`[fill="#…"]`, `[stroke="#…"]`, `[fill-opacity="…"]`) below the
  picture's id (an attribute selector for an id that starts with a digit), so the files are
  unchanged. A content policy must allow these `style` elements (`style-src 'unsafe-inline'`, or the
  hash of each); nothing else of an inline picture needs inline style.
* **Files.** Each inline picture names the file of the figures folder it is the body of
  (`data-pilean-file`), so a check of the published site can compare the two (PILean's
  `tools/site/inline_check.py`).
* **Explorers** (`explorerHtml`). Every frame is in the page, each in a list item that carries its
  value and its step caption as data attributes (`data-value-text`, `data-step-text`) and shows
  them under the picture. Without script the frames are a grid in their order, as many columns as
  fit, each picture with its value and step under it, the frame shown first with script outlined;
  no control is shown and nothing is focusable but the links of the pictures (in the link modes
  that have links). The script `pilean-explorer.js` (`explorerJs`, a
  file of the site; no network, no `eval`, no `innerHTML`; it runs under a content policy that
  allows the site's own scripts only) marks the root `pilean-explorer-live`, shows the controls (a
  slider for the parameter axis, previous, play and next for the steps, with a slider of their
  own when the steps are the values of a second parameter (`FrameSet.stepName`), zoom in, zoom
  out and reset), shows one frame at a time and makes the view a focusable group. Without script
  the poster comes first, across the whole width, and the other frames follow it. A frame of a
  different size keeps its own view box; pan and zoom are shared as fractions of each frame's box.
* **Gestures.** The page keeps its own scrolling, as embedded maps do with cooperative gestures:
  the wheel and a one-finger swipe scroll the page; Ctrl or ⌘ with the wheel (what a trackpad
  pinch sends) zooms about the pointer, and the wheel events that follow within 400 ms keep
  zooming, so a gesture under way does not turn into a scroll; two fingers pinch and pan; a mouse
  drag pans; on the focused view `+`, `-` and `0` zoom and reset and the arrows pan (with Ctrl, ⌘
  or Alt held, keys are left to the browser).
* **Motions** (`motionCss`; the markup is `PILeanVerso.motionHtml`). A motion's moving picture
  is an inline picture of its own, shown on its clock from the page's load; hovering or focusing
  it shows its poster's still in its box, and the page's `data-motion="reduce"`, the reader's
  `prefers-reduced-motion: reduce` and print show its stills with their captions instead. The
  moving picture is hidden by `visibility` or `opacity` (out of the flow where it must take no
  space), never by `display: none`, in print too, so that it follows its clock when it is shown
  again.
* **Announcements.** One polite status region per explorer says the step after previous or next
  (`Step 2 of 4: …`, or `a = 3` for a parameter); a slider says its value itself
  (`aria-valuetext`); nothing is announced when the page loads or while the steps play. A reader who
  asks for reduced motion gets no play
  button and no transitions.

## Main definitions

* `domSafe`, `prefixNode`, `inlineSvgText`, `themeCss`, `explorerHtml`, `explorerJs`, `explorerCss`.
* `motionCss`, `motionOffRules`, `motionHiddenRendition`: the stylesheet of motions shown in a page.
-/

namespace PILeanVerso

open PILean PILean.Trust

/-- The text of the first `title` child of an element, if it has one. -/
def titleOf (children : Array Svg.Node) : Option String :=
  children.findSome? fun
    | .element "title" _ #[.text t] => some t
    | _ => none

/-- `s` with every character other than an ASCII letter, a digit, `-` and `_` replaced by `_`:
an id that a selector and a URL fragment carry as it is. -/
def domSafe (s : String) : String :=
  s.map fun c => if (c.isAlphanum && c.toNat < 128) || c == '-' || c == '_' then c else '_'

/-- The node with every id prefixed by `pfx`, every reference to an id and every
`data-pilean-actor` likewise, and every element carrying `data-lean-decl` wrapped in a link to
the declaration when `href` gives one (the link's label is the element's title, or the
declaration's name). An element inside a link is not
linked again (`inLink`). -/
partial def prefixNode (pfx : String) (href : String → Option String) (inLink : Bool := false) :
    Svg.Node → Svg.Node
  | .text t => .text t
  | .element name attrs children =>
    let attrs := attrs.map fun (k, v) =>
      if k == "id" || k == "data-pilean-actor" then (k, pfx ++ v)
      else if k == "href" || k.endsWith ":href" then
        (k, if v.startsWith "#" then "#" ++ pfx ++ (v.drop 1).toString else v)
      else (k, v.replace "url(#" ("url(#" ++ pfx))
    let link := if inLink then none else
      (attrs.find? (·.1 == "data-lean-decl")).bind fun (_, d) => (href d).map (d, ·)
    let kids := children.map (prefixNode pfx href (inLink || link.isSome))
    let node := Svg.Node.element name attrs kids
    match link with
    | some (d, h) =>
      .element "a" #[("href", h), ("class", "pilean-decl-link"),
        ("aria-label", (titleOf kids).getD d)] #[node]
    | none => node

/-- The CSS that restyles an inline picture with the id `id` (`domSafe`) in the dark theme: each
light colour of `pairs` to its dark one, as a fill and as a stroke, and each tint opacity of
`opacities`, below the picture's id (`#id`, or `svg[id="…"]` for an id that does not start with
a letter, which an id selector cannot name without an escape). Empty when there is nothing to
restyle. -/
def themeCss (id : String) (pairs opacities : Array (String × String)) : String :=
  if pairs.isEmpty && opacities.isEmpty then ""
  else
    let id := domSafe id
    let sel := if (id.front).isAlpha then s!"#{id}" else s!"svg[id=\"{id}\"]"
    let rules := fun (pre : String) =>
      String.join (pairs.toList.map fun (a, b) =>
        s!"{pre} {sel} [fill=\"{a}\"]\{fill:{b}}{pre} {sel} [stroke=\"{a}\"]\{stroke:{b}}") ++
      String.join (opacities.toList.map fun (a, b) =>
        s!"{pre} {sel} [fill-opacity=\"{a}\"]\{fill-opacity:{b}}")
    rules "html[data-theme=\"dark\"]" ++ "@media (prefers-color-scheme: dark){" ++
      rules "html:not([data-theme=\"light\"])" ++ "}"

/-- An inline picture as the text of an `svg` element with the id `id` (`domSafe`; it prefixes
the picture's own ids, see `prefixNode`), the class `cls`, the accessible name `label`, its theme
rules in a `style` element, its declaration links (`href`), the path of its file in the
figures folder (`file`) and further attributes of the root (`attrs`). -/
def inlineSvgText (id : String) (i : InlineSvg) (href : String → Option String) (label : String)
    (cls : String := "") (file : Option String := none) (attrs : Array (String × String) := #[]) :
    String :=
  let id := domSafe id
  let w := fmtNum i.width
  let h := fmtNum i.height
  let css := themeCss id i.darkColours i.darkOpacities
  let style := if css.isEmpty then #[] else
    #[Svg.el "style" #[("class", "pilean-theme")] #[.text css]]
  let fileAttr := match file with
    | some f => #[("data-pilean-file", f)]
    | none => #[]
  let root := Svg.el "svg" (#[("xmlns", "http://www.w3.org/2000/svg"),
    ("class", ("pilean-inline-svg " ++ cls).trimAscii.toString), ("id", id),
    ("viewBox", s!"0 0 {w} {h}"), ("width", w), ("height", h), ("role", "img"),
    ("aria-label", label), ("data-view", s!"0 0 {w} {h}")] ++ fileAttr ++ attrs)
    (style ++ i.nodes.map (prefixNode (id ++ "-") href))
  Svg.render 0 root

/-- The value of frame `k` of an explorer, as its axis shows it (`8/10`); empty without an axis. -/
def frameValue (fs : FrameSet) (k : Nat) : String :=
  (fs.axisValues[k / max 1 fs.stepCaptions.size]?).getD ""

/-- The step caption of frame `k` of an explorer; empty without steps. -/
def frameStep (fs : FrameSet) (k : Nat) : String :=
  (fs.stepCaptions[k % max 1 fs.stepCaptions.size]?).getD ""

/-- The counter of frame `k` of an explorer (`Step 2 of 4`); empty without steps and when the
steps are the values of a parameter (`FrameSet.stepName`). -/
def frameCounter (fs : FrameSet) (k : Nat) : String :=
  if fs.stepCaptions.isEmpty || !fs.stepName.isEmpty then ""
  else s!"Step {k % fs.stepCaptions.size + 1} of {fs.stepCaptions.size}"

/-- What frame `k` says about its step: `Step 2 of 4: caption`, or `a = 3` when the steps are the
values of the parameter `a`; empty without steps. -/
def frameStepText (fs : FrameSet) (k : Nat) : String :=
  if fs.stepCaptions.isEmpty then ""
  else if fs.stepName.isEmpty then s!"{frameCounter fs k}: {frameStep fs k}"
  else s!"{fs.stepName} = {frameStep fs k}"

/-- The label of frame `k` of an explorer: its value (`r = 13/10`) and its step
(`frameStepText`). -/
def frameLabel (fs : FrameSet) (k : Nat) : String :=
  let value := if fs.axisValues.isEmpty then "" else s!"{fs.axisName} = {frameValue fs k}"
  " · ".intercalate ([value, frameStepText fs k].filter (!·.isEmpty))

/-- A small icon for a control button (hidden from assistive technology; the button's label
names it): a path in a 16 × 16 box, drawn in the text colour. -/
def iconSvg (d : String) (cls : String := "") : String :=
  let c := if cls.isEmpty then "" else s!" class=\"{cls}\""
  s!"<svg{c} viewBox=\"0 0 16 16\" width=\"16\" height=\"16\" aria-hidden=\"true\" \
    focusable=\"false\"><path d=\"{d}\" fill=\"currentColor\"/></svg>"

/-- The markup of an explorer (see the module docstring): `id` is unique in the page, `alt` the
text alternative, `href` the declaration links, `name` how the controls name the figure (`Figure
2.1`) and `file k` the path of frame `k`'s file in the figures folder, if it has one. -/
def explorerHtml (id : String) (fs : FrameSet) (href : String → Option String) (alt : String)
    (name : String := "the figure") (file : Nat → Option String := fun _ => none) : String :=
  let id := domSafe id
  let esc := escapeAttr
  let steps := max 1 fs.stepCaptions.size
  let values := max 1 fs.axisValues.size
  let pi := fs.poster / steps
  let frames := String.join (fs.frames.toList.zipIdx.map fun (f, k) =>
    let current := if k == fs.poster then " pilean-explorer-current" else ""
    let poster := if k == fs.poster then " data-poster=\"\"" else ""
    s!"<li class=\"pilean-explorer-frame{current}\" data-index=\"{k}\" data-value=\"{k / steps}\" \
      data-step=\"{k % steps}\"{poster} data-value-text=\"{esc (frameValue fs k)}\" \
      data-step-text=\"{esc (frameStep fs k)}\" data-counter=\"{esc (frameCounter fs k)}\" \
      data-step-say=\"{esc (frameStepText fs k)}\">" ++
      inlineSvgText s!"{id}-f{k}" f href s!"{alt} ({frameLabel fs k})" (file := file k) ++
      s!"<p class=\"pilean-explorer-frame-label\">{escapeText (frameLabel fs k)}</p></li>")
  let axis := if fs.axisValues.isEmpty then "" else
    let v := fs.axisValues[pi]?.getD ""
    s!"<label class=\"pilean-explorer-axis\"><span class=\"pilean-explorer-axis-name\">\
      {escapeText fs.axisName}</span>\
      <input type=\"range\" data-axis=\"value\" min=\"0\" max=\"{values - 1}\" step=\"1\" \
      value=\"{pi}\" aria-label=\"{esc s!"Value of {fs.axisName} in {name}"}\" \
      aria-valuetext=\"{esc v}\"/>\
      <span class=\"pilean-explorer-value\" aria-hidden=\"true\">{escapeText v}</span></label>"
  let pj := fs.poster % steps
  -- the steps as the values of a parameter: a slider beside the buttons
  let stepSlider := if fs.stepName.isEmpty then "" else
    let v := fs.stepCaptions[pj]?.getD ""
    s!"<label class=\"pilean-explorer-axis\"><span class=\"pilean-explorer-axis-name\">\
      {escapeText fs.stepName}</span>\
      <input type=\"range\" data-axis=\"step\" min=\"0\" max=\"{steps - 1}\" step=\"1\" \
      value=\"{pj}\" aria-label=\"{esc s!"Value of {fs.stepName} in {name}"}\" \
      aria-valuetext=\"{esc v}\"/>\
      <span class=\"pilean-explorer-step-value\" aria-hidden=\"true\">{escapeText v}</span></label>"
  let playName := if fs.stepName.isEmpty then "Play the steps" else s!"Play {fs.stepName}"
  let prevName :=
    if fs.stepName.isEmpty then "Previous step" else s!"Previous value of {fs.stepName}"
  let nextName := if fs.stepName.isEmpty then "Next step" else s!"Next value of {fs.stepName}"
  let stepper := if fs.stepCaptions.isEmpty then "" else
    s!"{stepSlider}<span class=\"pilean-explorer-steps\">\
      <button type=\"button\" data-action=\"prev\" aria-label=\"{esc prevName}\">\
      {iconSvg "M10.5 2.5 5 8l5.5 5.5 1.4-1.4L7.8 8l4.1-4.1z"}</button>\
      <button type=\"button\" data-action=\"play\" aria-label=\"{esc playName}\" \
      aria-pressed=\"false\">{iconSvg "M4 2.5v11L13 8z" "pilean-icon-play"}\
      {iconSvg "M3.5 2.5h3v11h-3zm6 0h3v11h-3z" "pilean-icon-pause"}</button>\
      <button type=\"button\" data-action=\"next\" aria-label=\"{esc nextName}\">\
      {iconSvg "M5.5 2.5 11 8l-5.5 5.5-1.4-1.4L8.2 8 4.1 3.9z"}</button>\
      <span class=\"pilean-explorer-counter\" aria-hidden=\"true\">\
      {escapeText (frameCounter fs fs.poster)}</span>\
      <span class=\"pilean-explorer-caption\" aria-hidden=\"true\">\
      {escapeText (if fs.stepName.isEmpty then frameStep fs fs.poster else "")}</span></span>"
  let zoom := s!"<span class=\"pilean-explorer-zoom\">\
    <button type=\"button\" data-action=\"zoom-in\" aria-label=\"Zoom in\">\
    {iconSvg "M7 2.5h2V7h4.5v2H9v4.5H7V9H2.5V7H7z"}</button>\
    <button type=\"button\" data-action=\"zoom-out\" aria-label=\"Zoom out\">\
    {iconSvg "M2.5 7h11v2h-11z"}</button>\
    <button type=\"button\" data-action=\"reset\" aria-label=\"Reset the view\">Reset</button>\
    </span>"
  let help := "Ctrl or Command with the wheel, or two fingers, zoom; a mouse drag pans; \
    the keys + and - zoom, 0 resets, the arrows pan."
  s!"<div class=\"pilean-explorer\" data-pilean-explorer=\"\" data-values=\"{values}\" \
    data-steps=\"{steps}\" data-poster=\"{fs.poster}\" data-label=\"{esc alt}\">\
    <div class=\"pilean-explorer-view\">\
    <ol class=\"pilean-explorer-frames\">{frames}</ol></div>\
    <p class=\"pilean-explorer-help\" id=\"{id}-help\" hidden=\"\">{escapeText help}</p>\
    <div class=\"pilean-explorer-controls\" hidden=\"\">{axis}{stepper}{zoom}\
    <span class=\"pilean-explorer-status\" role=\"status\" aria-live=\"polite\" \
    aria-atomic=\"true\"></span></div></div>"

/-- The script of explorers (see the module docstring), the file `pilean-explorer.js`. -/
def explorerJs : String := r##"// PILean explorers: one frame at a time, a slider, steps, pan, zoom.
// No network, no eval, no innerHTML: text is set with textContent and attributes.
(function () {
  "use strict";
  var reduced = window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches;
  var ZOOM_GESTURE_MS = 400;
  function parseBox(s) {
    var v = (s || "0 0 1 1").split(/[\s,]+/).map(Number);
    if (v.length !== 4 || v.some(function (n) { return !isFinite(n); }) || v[2] <= 0 || v[3] <= 0)
      return { x: 0, y: 0, w: 1, h: 1 };
    return { x: v[0], y: v[1], w: v[2], h: v[3] };
  }
  function setup(root) {
    if (root.classList.contains("pilean-explorer-live")) return;
    var frames = Array.prototype.slice.call(root.querySelectorAll(".pilean-explorer-frame"));
    if (frames.length === 0) return;
    var steps = Number(root.getAttribute("data-steps")) || 1;
    var poster = Number(root.getAttribute("data-poster")) || 0;
    var view = root.querySelector(".pilean-explorer-view");
    var controls = root.querySelector(".pilean-explorer-controls");
    var slider = root.querySelector("input[data-axis=value]");
    var valueOut = root.querySelector(".pilean-explorer-value");
    var stepSlider = root.querySelector("input[data-axis=step]");
    var stepOut = root.querySelector(".pilean-explorer-step-value");
    var counter = root.querySelector(".pilean-explorer-counter");
    var caption = root.querySelector(".pilean-explorer-caption");
    var status = root.querySelector(".pilean-explorer-status");
    var help = root.querySelector(".pilean-explorer-help");
    var play = root.querySelector("[data-action=play]");
    var svgs = frames.map(function (f) { return f.querySelector("svg"); });
    var homes = svgs.map(function (s) { return parseBox(s && s.getAttribute("data-view")); });
    // The view as fractions of each frame's own box.
    var rel = { x: 0, y: 0, w: 1, h: 1 };
    var vi = Math.floor(poster / steps), sj = poster % steps, timer = null, zoomUntil = 0;
    root.classList.add("pilean-explorer-live");
    if (controls) controls.hidden = false;
    if (play && reduced) play.hidden = true;
    view.tabIndex = 0;
    view.setAttribute("role", "group");
    view.setAttribute("aria-label", root.getAttribute("data-label") || "");
    if (help && help.id) view.setAttribute("aria-describedby", help.id);
    function data(k, name) { return frames[k] ? frames[k].getAttribute(name) || "" : ""; }
    function say(text) { if (status) status.textContent = text; }
    function show() {
      var k = vi * steps + sj;
      frames.forEach(function (f, i) { f.classList.toggle("pilean-explorer-current", i === k); });
      if (slider) {
        slider.value = String(vi);
        slider.setAttribute("aria-valuetext", data(k, "data-value-text"));
        if (valueOut) valueOut.textContent = data(k, "data-value-text");
      }
      if (stepSlider) {
        stepSlider.value = String(sj);
        stepSlider.setAttribute("aria-valuetext", data(k, "data-step-text"));
        if (stepOut) stepOut.textContent = data(k, "data-step-text");
      }
      if (counter) counter.textContent = data(k, "data-counter");
      if (caption && !stepSlider) caption.textContent = data(k, "data-step-text");
    }
    function stepText() { return data(vi * steps + sj, "data-step-say"); }
    function apply() {
      svgs.forEach(function (svg, i) {
        if (!svg) return;
        var h = homes[i];
        svg.setAttribute("viewBox", (h.x + rel.x * h.w) + " " + (h.y + rel.y * h.h) + " " +
          (rel.w * h.w) + " " + (rel.h * h.h));
      });
    }
    function clamp() {
      rel.x = Math.min(1 - rel.w / 2, Math.max(-rel.w / 2, rel.x));
      rel.y = Math.min(1 - rel.h / 2, Math.max(-rel.h / 2, rel.y));
    }
    function zoomAbout(fx, fy, factor) {
      var w = Math.min(1, Math.max(1 / 8, rel.w / factor));
      var k = w / rel.w;
      rel.x = fx - (fx - rel.x) * k; rel.y = fy - (fy - rel.y) * k;
      rel.w = w; rel.h = rel.h * k;
      clamp(); apply();
    }
    function centre() { return { x: rel.x + rel.w / 2, y: rel.y + rel.h / 2 }; }
    function currentRect() { return svgs[vi * steps + sj].getBoundingClientRect(); }
    function toRel(clientX, clientY) {
      var r = currentRect();
      if (!(r.width > 0 && r.height > 0)) return centre();
      return { x: rel.x + (clientX - r.left) / r.width * rel.w,
               y: rel.y + (clientY - r.top) / r.height * rel.h };
    }
    function panBy(dx, dy) {
      var r = currentRect();
      if (!(r.width > 0 && r.height > 0)) return;
      rel.x -= dx / r.width * rel.w; rel.y -= dy / r.height * rel.h;
      clamp(); apply();
    }
    function reset() { rel = { x: 0, y: 0, w: 1, h: 1 }; apply(); }
    function stop() {
      if (timer) { clearInterval(timer); timer = null; }
      if (status) status.setAttribute("aria-live", "polite");
      if (play) play.setAttribute("aria-pressed", "false");
    }
    if (slider) {
      slider.addEventListener("input", function () { vi = Number(slider.value); show(); });
    }
    if (stepSlider) {
      stepSlider.addEventListener("input", function () {
        stop(); sj = Number(stepSlider.value); show();
      });
    }
    root.addEventListener("click", function (ev) {
      var b = ev.target.closest ? ev.target.closest("[data-action]") : null;
      if (!b || !root.contains(b)) return;
      var a = b.getAttribute("data-action");
      if (a === "prev") { stop(); sj = (sj + steps - 1) % steps; show(); say(stepText()); }
      else if (a === "next") { stop(); sj = (sj + 1) % steps; show(); say(stepText()); }
      else if (a === "play") {
        if (timer) stop();
        else {
          if (status) status.setAttribute("aria-live", "off");
          play.setAttribute("aria-pressed", "true");
          timer = setInterval(function () { sj = (sj + 1) % steps; show(); }, 1400);
        }
      }
      else if (a === "zoom-in") { var c = centre(); zoomAbout(c.x, c.y, 1.25); }
      else if (a === "zoom-out") { var d = centre(); zoomAbout(d.x, d.y, 0.8); }
      else if (a === "reset") reset();
    });
    view.addEventListener("wheel", function (ev) {
      var now = Date.now();
      if (!(ev.ctrlKey || ev.metaKey) && now > zoomUntil) return;
      ev.preventDefault();
      zoomUntil = now + ZOOM_GESTURE_MS;
      var p = toRel(ev.clientX, ev.clientY);
      zoomAbout(p.x, p.y, Math.exp(-ev.deltaY * (ev.ctrlKey ? 0.01 : 0.0015)));
    }, { passive: false });
    // Two fingers zoom and pan the picture; one finger is left to the page.
    view.addEventListener("touchmove", function (ev) {
      if (ev.touches && ev.touches.length >= 2 && ev.cancelable) ev.preventDefault();
    }, { passive: false });
    var mouse = null, touches = {}, pinch = null;
    view.addEventListener("pointerdown", function (ev) {
      if (ev.target.closest && ev.target.closest("a")) return;
      if (ev.pointerType === "touch") {
        touches[ev.pointerId] = { x: ev.clientX, y: ev.clientY };
        pinch = null;
        return;
      }
      if (ev.button !== 0) return;
      mouse = { id: ev.pointerId, x: ev.clientX, y: ev.clientY };
      if (view.setPointerCapture) view.setPointerCapture(ev.pointerId);
    });
    view.addEventListener("pointermove", function (ev) {
      if (ev.pointerType === "touch") {
        if (!touches[ev.pointerId]) return;
        touches[ev.pointerId] = { x: ev.clientX, y: ev.clientY };
        var ids = Object.keys(touches);
        if (ids.length !== 2) return;
        var a = touches[ids[0]], b = touches[ids[1]];
        var mid = { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 };
        var dist = Math.hypot(a.x - b.x, a.y - b.y);
        if (pinch && pinch.dist > 0 && dist > 0) {
          panBy(mid.x - pinch.x, mid.y - pinch.y);
          var p = toRel(mid.x, mid.y);
          zoomAbout(p.x, p.y, dist / pinch.dist);
        }
        pinch = { x: mid.x, y: mid.y, dist: dist };
        return;
      }
      if (!mouse || mouse.id !== ev.pointerId) return;
      panBy(ev.clientX - mouse.x, ev.clientY - mouse.y);
      mouse.x = ev.clientX; mouse.y = ev.clientY;
    });
    function up(ev) {
      if (ev.pointerType === "touch") { delete touches[ev.pointerId]; pinch = null; }
      else if (mouse && mouse.id === ev.pointerId) mouse = null;
    }
    view.addEventListener("pointerup", up);
    view.addEventListener("pointercancel", up);
    view.addEventListener("keydown", function (ev) {
      if (ev.ctrlKey || ev.metaKey || ev.altKey) return;
      var c = centre(), step = rel.w / 10, done = true;
      switch (ev.key) {
        case "+": case "=": zoomAbout(c.x, c.y, 1.25); break;
        case "-": case "_": zoomAbout(c.x, c.y, 0.8); break;
        case "0": reset(); break;
        case "ArrowLeft": rel.x -= step; clamp(); apply(); break;
        case "ArrowRight": rel.x += step; clamp(); apply(); break;
        case "ArrowUp": rel.y -= step; clamp(); apply(); break;
        case "ArrowDown": rel.y += step; clamp(); apply(); break;
        default: done = false;
      }
      if (done) ev.preventDefault();
    });
    show();
  }
  function start() {
    Array.prototype.forEach.call(document.querySelectorAll("[data-pilean-explorer]"), setup);
  }
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", start);
  else start();
})();
"##

/-- The stylesheet of inline pictures and explorers. Everything is centred in its container and
kept within its width, also in a narrow column. -/
def explorerCss : String := r##"
.pilean-inline-svg {
  display: block; max-width: 100%; height: auto; margin-left: auto; margin-right: auto;
}
.pilean-inline-frame { display: flex; justify-content: center; max-width: 100%; min-width: 0; }
.pilean-inline-frame > .pilean-inline-svg { min-width: 0; }
.pilean-inline-narrow { display: none; }
@media (max-width: 560px) {
  .pilean-has-narrow .pilean-inline-wide { display: none; }
  .pilean-has-narrow .pilean-inline-narrow { display: flex; }
}
.pilean-has-narrow { width: 100%; min-width: 0; }
a.pilean-decl-link { cursor: pointer; }
a.pilean-decl-link:focus { outline: none; }
a.pilean-decl-link:focus-visible {
  outline: 3px solid var(--pilean-focus, #2563eb); outline-offset: 2px;
}
a.pilean-decl-link:focus-visible > * { stroke: var(--pilean-focus, #2563eb); }
.pilean-explorer { width: 100%; max-width: 100%; min-width: 0; box-sizing: border-box; }
.pilean-explorer-view { max-width: 100%; border-radius: 6px; }
.pilean-explorer-live .pilean-explorer-view { touch-action: pan-x pan-y; }
.pilean-explorer-view:focus-visible {
  outline: 3px solid var(--pilean-focus, #2563eb); outline-offset: 2px;
}
.pilean-explorer-frames {
  list-style: none; margin: 0; padding: 0;
  display: grid; grid-template-columns: repeat(auto-fit, minmax(min(14rem, 100%), 1fr));
  gap: 0.75rem; justify-items: center;
}
.pilean-explorer-frame { margin: 0; min-width: 0; max-width: 100%; }
.pilean-explorer:not(.pilean-explorer-live) .pilean-explorer-frame[data-poster] {
  outline: 2px solid var(--pilean-rule, #d9dce3); outline-offset: 4px; border-radius: 4px;
  order: -1; grid-column: 1 / -1;
}
.pilean-explorer-frame-label { margin: 0.2rem 0 0; font-size: 0.85em; text-align: center; }
.pilean-explorer-live .pilean-explorer-frames { display: block; }
.pilean-explorer-live .pilean-explorer-frame { display: none; }
.pilean-explorer-live .pilean-explorer-frame.pilean-explorer-current { display: block; }
.pilean-explorer-live .pilean-explorer-frame-label, .pilean-explorer-status {
  position: absolute; width: 1px; height: 1px; margin: -1px; padding: 0; border: 0;
  overflow: hidden; clip: rect(0 0 0 0); white-space: nowrap;
}
.pilean-explorer-controls {
  display: flex; flex-wrap: wrap; align-items: center; justify-content: center;
  gap: 0.4rem 0.9rem; margin-top: 0.5rem; font-size: 0.92em; max-width: 100%;
  text-align: center;
}
.pilean-explorer-controls[hidden] { display: none; }
.pilean-explorer-axis {
  display: inline-flex; align-items: center; gap: 0.5rem; max-width: 100%; min-width: 0;
}
.pilean-explorer-axis input {
  width: 16rem; max-width: 100%; min-width: 5rem; flex: 1 1 auto; height: 2.75rem; margin: 0;
}
.pilean-explorer-axis-name { min-width: 0; overflow-wrap: anywhere; }
.pilean-explorer-value, .pilean-explorer-step-value {
  font-variant-numeric: tabular-nums; min-width: 3ch; overflow-wrap: anywhere;
}
.pilean-explorer-controls button {
  display: inline-flex; align-items: center; justify-content: center;
  min-width: 2.75rem; min-height: 2.75rem; padding: 0.2rem 0.6rem; border-radius: 6px;
  border: 1px solid var(--pilean-rule, #d9dce3); background: transparent; color: inherit;
  font: inherit; cursor: pointer;
}
.pilean-explorer-controls button[hidden] { display: none; }
.pilean-explorer-controls button svg { width: 1.1rem; height: 1.1rem; }
.pilean-explorer-controls button[aria-pressed="true"] .pilean-icon-play,
.pilean-explorer-controls button[aria-pressed="false"] .pilean-icon-pause { display: none; }
.pilean-explorer-controls button:focus-visible,
.pilean-explorer-controls input:focus-visible {
  outline: 3px solid var(--pilean-focus, #2563eb); outline-offset: 2px;
}
.pilean-explorer-steps, .pilean-explorer-zoom {
  display: inline-flex; flex-wrap: wrap; align-items: center; justify-content: center;
  gap: 0.3rem; max-width: 100%;
}
.pilean-explorer-counter { font-variant-numeric: tabular-nums; }
.pilean-explorer-caption { font-style: italic; overflow-wrap: anywhere; }
@media (prefers-reduced-motion: reduce) {
  .pilean-explorer *, .pilean-inline-svg * {
    transition: none !important; animation: none !important;
  }
}
"##

/-- The rules that turn a motion's animation off, below the selector prefix `pre`
(`html[data-motion="reduce"] ` for the motion switch, empty inside a media query): the stage is
hidden and taken out of the flow and the stills are shown as a grid with their captions; a motion
shown without its stills (`pilean-motion-bare`, on the figure's page, whose stills are shown
below it) keeps its stage and shows the poster's still over the moving picture; the caption's
hint about pausing is hidden. The moving picture is hidden by `visibility` or `opacity`, never by
`display: none`, also in print: an inline SVG animation that is not rendered can stay frozen when
it is shown again, although its clock runs. -/
def motionOffRules (pre : String) : String :=
  s!"{pre}.pilean-motion:not(.pilean-motion-bare) .pilean-motion-stage \{visibility:hidden;\
    position:absolute;top:0;left:0;pointer-events:none}\
    {pre}.pilean-motion-bare svg.pilean-motion-live \{opacity:0}\
    {pre}.pilean-motion-bare .pilean-motion-still \{opacity:1}\
    {pre}.pilean-motion-keys \{position:static;width:auto;height:auto;margin:0;overflow:visible;\
    clip:auto;clip-path:none;white-space:normal;display:grid;\
    grid-template-columns:repeat(auto-fit,minmax(min(14rem,100%),1fr));gap:0.75rem;\
    justify-items:center;align-items:start}\
    {pre}.pilean-motion-key-pic \{display:block}\
    {pre}.pilean-motion-hint \{display:none}"

/-- The rules of the hidden rendition of a motion (the narrow one on wide screens, the wide one
on small screens): kept rendered, so that its clock keeps the picture in step, but invisible and
out of the flow. -/
def motionHiddenRendition : String :=
  "{visibility:hidden;position:absolute;top:0;left:0;pointer-events:none}"

/-- The stylesheet of motions shown in a page (`PILeanVerso.motionHtml`), scoped under
`.pilean-motion`. While motion is on, the moving picture is shown and the key stills' captions
are kept for assistive technology only (visually hidden; their pictures are not drawn). Hovering
the picture (on a device that hovers) or focusing it (by the keyboard, a click or a tap) shows the
poster key's still in the picture's own box instead, so nothing around it moves; the moving
picture is then only made transparent, so its text alternative stays in the accessibility tree,
and the focused stage has a ring in `--pilean-focus`. Motion is off under the page's
`data-motion="reduce"` (the Verso Blueprint motion switch), under the reader's
`prefers-reduced-motion: reduce`, and in print (`motionOffRules`). The narrow rendition is shown
on small screens (the plane figures' breakpoint, 560 pixels), the wide one elsewhere
(`motionHiddenRendition`). No rule needs a script, and none depends on the Blueprint's own
classes. -/
def motionCss : String :=
  ".pilean-motion{position:relative;width:100%;max-width:100%;min-width:0}\
  .pilean-motion-stage{position:relative;width:fit-content;max-width:100%;margin:0 auto;\
    border-radius:6px}\
  .pilean-motion-stage:focus{outline:3px solid var(--pilean-focus);outline-offset:4px}\
  .pilean-motion svg.pilean-motion-live{display:block;max-width:100%;height:auto;margin:0 auto}\
  .pilean-motion-sized svg.pilean-motion-live{width:100%}\
  @media not all and (max-width: 560px){.pilean-motion svg.pilean-motion-narrow" ++
    motionHiddenRendition ++ "}\
  @media (max-width: 560px){.pilean-motion-has-narrow svg.pilean-motion-wide" ++
    motionHiddenRendition ++ "}\
  .pilean-motion-still{position:absolute;inset:0;opacity:0;pointer-events:none}\
  .pilean-motion-still img{position:absolute;inset:0;display:block;width:100%;height:100%}\
  @media (hover: hover){\
    .pilean-motion-stage:hover svg.pilean-motion-live{opacity:0}\
    .pilean-motion-stage:hover .pilean-motion-still{opacity:1}}\
  .pilean-motion-stage:focus svg.pilean-motion-live{opacity:0}\
  .pilean-motion-stage:focus .pilean-motion-still{opacity:1}\
  .pilean-motion-keys{list-style:none;padding:0;position:absolute;width:1px;height:1px;\
    margin:-1px;border:0;overflow:hidden;clip:rect(0 0 0 0);clip-path:inset(50%);\
    white-space:nowrap}\
  .pilean-motion-key{margin:0;min-width:0;max-width:100%;text-align:center}\
  .pilean-motion-key-pic{display:none}\
  .pilean-motion-key-pic img{display:block;max-width:100%;height:auto;margin:0 auto;\
    border-radius:4px}\
  .pilean-motion-key-caption{margin:0.2rem 0 0;font-size:0.85em;overflow-wrap:anywhere}\
  .pilean-motion-note{display:block;font-size:0.85em;color:var(--pilean-muted, inherit)}" ++
  motionOffRules "html[data-motion=\"reduce\"] " ++
  "@media (prefers-reduced-motion: reduce){" ++ motionOffRules "" ++ "}" ++
  "@media print{" ++ motionOffRules "" ++ "}"

end PILeanVerso
