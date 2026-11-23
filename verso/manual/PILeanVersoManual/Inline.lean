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
element with a `data-lean-decl` becomes a link to its declaration (the href the document gives
for a declaration, `DeclStyle.href`), with a visible focus ring.

* **Ids.** Every `id` of a picture, and every `url(#…)` and `#…` reference to one, gets a prefix
  unique in the page (`prefixNode`), so that several pictures can share a page.
* **Themes.** One inline picture serves both themes: a `style` element inside it restyles its
  light colours to its dark twin's (`InlineSvg.darkColours`, `darkOpacities`) under the page's
  `data-theme="dark"`, or the system's dark scheme when the page does not say `light` (the
  selectors the `-dark` files use). Rules match the presentation attributes the writer emits
  (`[fill="#…"]`, `[stroke="#…"]`, `[fill-opacity="…"]`), so the files are unchanged.
* **Explorers** (`explorerHtml`). Every frame is in the page, each in a list item with its value
  and step caption under it; without script the list is a strip of all the frames, the poster
  marked. The script `pilean-explorer.js` (`explorerJs`, a file of the site; no network, no
  `eval`, it runs under a content policy that allows the site's own scripts only) marks the root
  `pilean-explorer-live`, shows the controls (a slider for the parameter axis, previous, play
  and next for the steps, zoom buttons), shows one frame at a time, and pans and zooms the frames'
  view box: the wheel zooms about the pointer, two fingers pinch, a drag pans, and the keys `+`,
  `-`, `0` and the arrows act on the focused view. A reader who asks for reduced motion gets no
  play button and no transitions.

## Main definitions

* `prefixNode`, `inlineSvgText`, `themeCss`, `explorerHtml`, `explorerJs`, `explorerCss`.
-/

namespace PILeanVerso

open PILean PILean.Trust

/-- The text of the first `title` child of an element, if it has one. -/
def titleOf (children : Array Svg.Node) : Option String :=
  children.findSome? fun
    | .element "title" _ #[.text t] => some t
    | _ => none

/-- The node with every id prefixed by `pfx`, every reference to an id likewise, and every
element carrying `data-lean-decl` wrapped in a link to the declaration when `href` gives one (the
link's label is the element's title, or the declaration's name). -/
partial def prefixNode (pfx : String) (href : String → Option String) : Svg.Node → Svg.Node
  | .text t => .text t
  | .element name attrs children =>
    let attrs := attrs.map fun (k, v) =>
      if k == "id" then (k, pfx ++ v)
      else if k == "href" || k.endsWith ":href" then
        (k, if v.startsWith "#" then "#" ++ pfx ++ (v.drop 1).toString else v)
      else (k, v.replace "url(#" ("url(#" ++ pfx))
    let kids := children.map (prefixNode pfx href)
    let node := Svg.Node.element name attrs kids
    match (attrs.find? (·.1 == "data-lean-decl")).bind fun (_, d) => (href d).map (d, ·) with
    | some (d, h) =>
      .element "a" #[("href", h), ("class", "pilean-decl-link"),
        ("aria-label", (titleOf kids).getD d)] #[node]
    | none => node

/-- The CSS that restyles an inline picture with the id `id` in the dark theme: each light colour
of `pairs` to its dark one, as a fill and as a stroke, and each tint opacity of `opacities`. Empty
when there is nothing to restyle. -/
def themeCss (id : String) (pairs opacities : Array (String × String)) : String :=
  if pairs.isEmpty && opacities.isEmpty then ""
  else
    let rules := fun (pre : String) =>
      String.join (pairs.toList.map fun (a, b) =>
        s!"{pre} #{id} [fill=\"{a}\"]\{fill:{b}}{pre} #{id} [stroke=\"{a}\"]\{stroke:{b}}") ++
      String.join (opacities.toList.map fun (a, b) =>
        s!"{pre} #{id} [fill-opacity=\"{a}\"]\{fill-opacity:{b}}")
    rules "html[data-theme=\"dark\"]" ++ "@media (prefers-color-scheme: dark){" ++
      rules "html:not([data-theme=\"light\"])" ++ "}"

/-- An inline picture as the text of an `svg` element with the id `id` (which prefixes its own
ids, see `prefixNode`), the class `cls`, the accessible name `label`, its theme rules in a
`style` element, and its declaration links (`href`). -/
def inlineSvgText (id : String) (i : InlineSvg) (href : String → Option String) (label : String)
    (cls : String := "") : String :=
  let w := fmtNum i.width
  let h := fmtNum i.height
  let css := themeCss id i.darkColours i.darkOpacities
  let style := if css.isEmpty then #[] else #[Svg.el "style" #[] #[.text css]]
  let root := Svg.el "svg" #[("xmlns", "http://www.w3.org/2000/svg"),
    ("class", ("pilean-inline-svg " ++ cls).trimAscii.toString), ("id", id),
    ("viewBox", s!"0 0 {w} {h}"), ("width", w), ("height", h), ("role", "img"),
    ("aria-label", label), ("data-view", s!"0 0 {w} {h}")]
    (style ++ i.nodes.map (prefixNode (id ++ "-") href))
  Svg.render 0 root

/-- The label of frame `k` of an explorer: its value (`r = 13/10`) and its step caption. -/
def frameLabel (fs : FrameSet) (k : Nat) : String :=
  let steps := max 1 fs.stepCaptions.size
  let i := k / steps
  let j := k % steps
  let value := match fs.axisValues[i]? with
    | some v => s!"{fs.axisName} = {v}"
    | none => ""
  let step := match fs.stepCaptions[j]? with
    | some c => s!"Step {j + 1} of {fs.stepCaptions.size}: {c}"
    | none => ""
  " · ".intercalate ([value, step].filter (!·.isEmpty))

/-- The markup of an explorer (see the module docstring): `id` is unique in the page, `alt` the
text alternative, `href` the declaration links. -/
def explorerHtml (id : String) (fs : FrameSet) (href : String → Option String) (alt : String) :
    String :=
  let esc := escapeAttr
  let steps := max 1 fs.stepCaptions.size
  let values := max 1 fs.axisValues.size
  let pi := fs.poster / steps
  let pj := fs.poster % steps
  let frames := String.join (fs.frames.toList.zipIdx.map fun (f, k) =>
    let current := if k == fs.poster then " pilean-explorer-current" else ""
    let poster := if k == fs.poster then " data-poster=\"\"" else ""
    s!"<li class=\"pilean-explorer-frame{current}\" data-index=\"{k}\" data-value=\"{k / steps}\" \
      data-step=\"{k % steps}\"{poster}>" ++
      inlineSvgText s!"{id}-f{k}" f href s!"{alt} ({frameLabel fs k})" ++
      s!"<p class=\"pilean-explorer-frame-label\">{escapeText (frameLabel fs k)}</p></li>")
  let axis := if fs.axisValues.isEmpty then "" else
    let v := fs.axisValues[pi]?.getD ""
    s!"<label class=\"pilean-explorer-axis\"><span>{escapeText fs.axisName}</span> \
      <input type=\"range\" min=\"0\" max=\"{values - 1}\" step=\"1\" value=\"{pi}\" \
      aria-label=\"{esc fs.axisName}\" aria-valuetext=\"{esc v}\"/></label>\
      <output class=\"pilean-explorer-value\" aria-live=\"polite\">{escapeText v}</output>"
  let stepper := if fs.stepCaptions.isEmpty then "" else
    let c := fs.stepCaptions[pj]?.getD ""
    s!"<span class=\"pilean-explorer-steps\">\
      <button type=\"button\" data-action=\"prev\" aria-label=\"Previous step\">‹</button>\
      <button type=\"button\" data-action=\"play\" aria-label=\"Play the steps\" \
      aria-pressed=\"false\">▶</button>\
      <button type=\"button\" data-action=\"next\" aria-label=\"Next step\">›</button>\
      <span class=\"pilean-explorer-counter\">Step {pj + 1} of {fs.stepCaptions.size}</span>\
      <span class=\"pilean-explorer-caption\" aria-live=\"polite\">{escapeText c}</span></span>"
  let zoom := "<span class=\"pilean-explorer-zoom\">\
    <button type=\"button\" data-action=\"zoom-in\" aria-label=\"Zoom in\">+</button>\
    <button type=\"button\" data-action=\"zoom-out\" aria-label=\"Zoom out\">−</button>\
    <button type=\"button\" data-action=\"reset\" aria-label=\"Reset the view\">Reset</button>\
    </span>"
  s!"<div class=\"pilean-explorer\" data-pilean-explorer=\"\" data-values=\"{values}\" \
    data-steps=\"{steps}\" data-poster=\"{fs.poster}\">\
    <div class=\"pilean-explorer-view\" tabindex=\"0\" role=\"group\" aria-label=\"{esc alt}. \
    Drag to pan; the wheel, + and - zoom; 0 resets.\">\
    <ol class=\"pilean-explorer-frames\">{frames}</ol></div>\
    <div class=\"pilean-explorer-controls\" hidden=\"\">{axis}{stepper}{zoom}</div></div>"

/-- The script of explorers (see the module docstring), the file `pilean-explorer.js`. -/
def explorerJs : String := r##"// PILean explorers: one frame at a time, a slider, steps, pan and zoom. No network, no eval.
(function () {
  "use strict";
  var reduced = window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches;
  function parseBox(s) {
    var v = (s || "0 0 1 1").split(/[\s,]+/).map(Number);
    return { x: v[0], y: v[1], w: v[2], h: v[3] };
  }
  function setup(root) {
    var frames = Array.prototype.slice.call(root.querySelectorAll(".pilean-explorer-frame"));
    if (frames.length === 0) return;
    var steps = Number(root.getAttribute("data-steps")) || 1;
    var poster = Number(root.getAttribute("data-poster")) || 0;
    var view = root.querySelector(".pilean-explorer-view");
    var controls = root.querySelector(".pilean-explorer-controls");
    var slider = root.querySelector("input[type=range]");
    var valueOut = root.querySelector(".pilean-explorer-value");
    var counter = root.querySelector(".pilean-explorer-counter");
    var caption = root.querySelector(".pilean-explorer-caption");
    var play = root.querySelector("[data-action=play]");
    var svgs = frames.map(function (f) { return f.querySelector("svg"); });
    var home = parseBox(svgs[0] && svgs[0].getAttribute("data-view"));
    var box = { x: home.x, y: home.y, w: home.w, h: home.h };
    var vi = Math.floor(poster / steps), sj = poster % steps, timer = null;
    root.classList.add("pilean-explorer-live");
    if (controls) controls.hidden = false;
    if (play && reduced) play.hidden = true;
    function labels(k) {
      var p = frames[k].querySelector(".pilean-explorer-frame-label");
      return p ? p.textContent : "";
    }
    function show() {
      var k = vi * steps + sj;
      frames.forEach(function (f, i) { f.classList.toggle("pilean-explorer-current", i === k); });
      if (slider) {
        slider.value = String(vi);
        var v = (labels(k).split(" · ")[0] || "").replace(/^.* = /, "");
        slider.setAttribute("aria-valuetext", v);
        if (valueOut) valueOut.textContent = v;
      }
      if (counter && caption) {
        var text = labels(k).split(" · ").pop() || "";
        var m = /^Step (\d+) of (\d+): (.*)$/.exec(text);
        if (m) { counter.textContent = "Step " + m[1] + " of " + m[2]; caption.textContent = m[3]; }
      }
    }
    function apply() {
      var s = box.x + " " + box.y + " " + box.w + " " + box.h;
      svgs.forEach(function (svg) { if (svg) svg.setAttribute("viewBox", s); });
    }
    function zoomAbout(px, py, factor) {
      var w = Math.min(home.w, Math.max(home.w / 8, box.w / factor));
      var k = w / box.w;
      box.x = px - (px - box.x) * k; box.y = py - (py - box.y) * k;
      box.w = w; box.h = box.h * k;
      clamp(); apply();
    }
    function clamp() {
      box.x = Math.min(home.x + home.w - box.w / 2, Math.max(home.x - box.w / 2, box.x));
      box.y = Math.min(home.y + home.h - box.h / 2, Math.max(home.y - box.h / 2, box.y));
    }
    function centre() { return { x: box.x + box.w / 2, y: box.y + box.h / 2 }; }
    function toBox(ev) {
      var svg = svgs[vi * steps + sj];
      var r = svg.getBoundingClientRect();
      return { x: box.x + (ev.clientX - r.left) / r.width * box.w,
               y: box.y + (ev.clientY - r.top) / r.height * box.h, r: r };
    }
    function reset() { box = { x: home.x, y: home.y, w: home.w, h: home.h }; apply(); }
    function stop() {
      if (timer) { clearInterval(timer); timer = null; }
      if (play) { play.setAttribute("aria-pressed", "false"); play.textContent = "▶"; }
    }
    if (slider) {
      slider.addEventListener("input", function () { vi = Number(slider.value); show(); });
    }
    root.addEventListener("click", function (ev) {
      var b = ev.target.closest ? ev.target.closest("[data-action]") : null;
      if (!b || !root.contains(b)) return;
      var a = b.getAttribute("data-action");
      if (a === "prev") { stop(); sj = (sj + steps - 1) % steps; show(); }
      else if (a === "next") { stop(); sj = (sj + 1) % steps; show(); }
      else if (a === "play") {
        if (timer) stop();
        else {
          play.setAttribute("aria-pressed", "true"); play.textContent = "❚❚";
          timer = setInterval(function () { sj = (sj + 1) % steps; show(); }, 1400);
        }
      }
      else if (a === "zoom-in") { var c = centre(); zoomAbout(c.x, c.y, 1.25); }
      else if (a === "zoom-out") { var d = centre(); zoomAbout(d.x, d.y, 0.8); }
      else if (a === "reset") reset();
    });
    view.addEventListener("wheel", function (ev) {
      ev.preventDefault();
      var p = toBox(ev);
      zoomAbout(p.x, p.y, Math.exp(-ev.deltaY * (ev.ctrlKey ? 0.01 : 0.0015)));
    }, { passive: false });
    var pointers = {}, pinch = 0;
    view.addEventListener("pointerdown", function (ev) {
      if (ev.target.closest && ev.target.closest("a")) return;
      pointers[ev.pointerId] = { x: ev.clientX, y: ev.clientY };
      if (view.setPointerCapture) view.setPointerCapture(ev.pointerId);
    });
    view.addEventListener("pointermove", function (ev) {
      var last = pointers[ev.pointerId];
      if (!last) return;
      var ids = Object.keys(pointers);
      var r = svgs[vi * steps + sj].getBoundingClientRect();
      if (ids.length === 2) {
        pointers[ev.pointerId] = { x: ev.clientX, y: ev.clientY };
        var a = pointers[ids[0]], b = pointers[ids[1]];
        var dist = Math.hypot(a.x - b.x, a.y - b.y);
        if (pinch > 0 && dist > 0) {
          var mid = toBox({ clientX: (a.x + b.x) / 2, clientY: (a.y + b.y) / 2 });
          zoomAbout(mid.x, mid.y, dist / pinch);
        }
        pinch = dist;
        return;
      }
      box.x -= (ev.clientX - last.x) / r.width * box.w;
      box.y -= (ev.clientY - last.y) / r.height * box.h;
      pointers[ev.pointerId] = { x: ev.clientX, y: ev.clientY };
      clamp(); apply();
    });
    function up(ev) { delete pointers[ev.pointerId]; pinch = 0; }
    view.addEventListener("pointerup", up);
    view.addEventListener("pointercancel", up);
    view.addEventListener("keydown", function (ev) {
      var c = centre(), step = box.w / 10, done = true;
      switch (ev.key) {
        case "+": case "=": zoomAbout(c.x, c.y, 1.25); break;
        case "-": case "_": zoomAbout(c.x, c.y, 0.8); break;
        case "0": reset(); break;
        case "ArrowLeft": box.x -= step; clamp(); apply(); break;
        case "ArrowRight": box.x += step; clamp(); apply(); break;
        case "ArrowUp": box.y -= step; clamp(); apply(); break;
        case "ArrowDown": box.y += step; clamp(); apply(); break;
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

/-- The stylesheet of inline pictures and explorers. -/
def explorerCss : String := r##"
.pilean-inline-svg { display: block; max-width: 100%; height: auto; }
.pilean-inline-frame { display: flex; justify-content: center; max-width: 100%; }
.pilean-inline-narrow { display: none; }
@media (max-width: 560px) {
  .pilean-has-narrow .pilean-inline-wide { display: none; }
  .pilean-has-narrow .pilean-inline-narrow { display: flex; }
}
a.pilean-decl-link { cursor: pointer; }
a.pilean-decl-link:focus { outline: none; }
a.pilean-decl-link:focus-visible {
  outline: 3px solid var(--pilean-focus, #2563eb); outline-offset: 2px;
}
a.pilean-decl-link:focus-visible > * { stroke: var(--pilean-focus, #2563eb); }
.pilean-explorer { max-width: 100%; }
.pilean-explorer-view { max-width: 100%; touch-action: none; border-radius: 6px; }
.pilean-explorer-view:focus-visible {
  outline: 3px solid var(--pilean-focus, #2563eb); outline-offset: 2px;
}
.pilean-explorer-frames {
  list-style: none; margin: 0; padding: 0;
  display: grid; grid-template-columns: repeat(auto-fill, minmax(14rem, 1fr)); gap: 0.75rem;
}
.pilean-explorer-frame { margin: 0; min-width: 0; }
.pilean-explorer-frame[data-poster] { grid-column: 1 / -1; }
.pilean-explorer-frame-label { margin: 0.2rem 0 0; font-size: 0.85em; text-align: center; }
.pilean-explorer-live .pilean-explorer-frames { display: block; }
.pilean-explorer-live .pilean-explorer-frame { display: none; }
.pilean-explorer-live .pilean-explorer-frame.pilean-explorer-current { display: block; }
.pilean-explorer-live .pilean-explorer-frame-label {
  position: absolute; width: 1px; height: 1px; overflow: hidden; clip: rect(0 0 0 0);
}
.pilean-explorer-controls {
  display: flex; flex-wrap: wrap; align-items: center; justify-content: center;
  gap: 0.4rem 0.9rem; margin-top: 0.5rem; font-size: 0.92em;
}
.pilean-explorer-controls[hidden] { display: none; }
.pilean-explorer-axis { display: inline-flex; align-items: center; gap: 0.4rem; }
.pilean-explorer-axis input { width: min(16rem, 60vw); }
.pilean-explorer-controls button {
  min-width: 2.2rem; min-height: 2.2rem; padding: 0.15rem 0.5rem; border-radius: 6px;
  border: 1px solid var(--pilean-rule, #d9dce3); background: transparent; color: inherit;
  font: inherit; cursor: pointer;
}
.pilean-explorer-controls button:focus-visible,
.pilean-explorer-controls input:focus-visible {
  outline: 3px solid var(--pilean-focus, #2563eb); outline-offset: 2px;
}
.pilean-explorer-steps, .pilean-explorer-zoom {
  display: inline-flex; align-items: center; gap: 0.3rem;
}
.pilean-explorer-counter { font-variant-numeric: tabular-nums; }
.pilean-explorer-caption { font-style: italic; }
@media (prefers-reduced-motion: reduce) {
  .pilean-explorer *, .pilean-inline-svg * {
    transition: none !important; animation: none !important;
  }
}
"##

end PILeanVerso
