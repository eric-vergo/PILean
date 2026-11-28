/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# The figures' stylesheet

One stylesheet for the figure blocks and the figures page. Colours come from the Blueprint's
tokens (`--bp-color-*`) when the page has them, with plain fallbacks for other Manual-genre
documents. A figure with a backdrop is laid over the backdrop's picture at the same size. The
dark picture of a figure (and of its backdrop) is shown when the page's root has
`data-theme="dark"`, or when the system prefers dark and the root does not have
`data-theme="light"`: the rules the Blueprint's and Verso's dark themes follow, without a script.
The focus ring's colour (`--pilean-focus`) follows the theme too, at more than 3:1 against the
light and the dark page.
The `lean:` links are shown only when the root has `data-lean-links` (a viewer that handles them
sets it); otherwise the declaration is plain code. A caption and the figures page break a word
too long for the column anywhere rather than widen the page. A caption is the author's text,
shown as written: like every block of a page it is isolated from the text around it, so
direction controls in it reorder only the caption (the labels drawn in pictures drop them,
`Plane.labelText`).
-/

namespace PILeanVerso

/-- The stylesheet of the figure blocks and the figures page. -/
def figureCss : String := r##"
:root {
  --pilean-muted: var(--bp-color-text-muted, #5b6170);
  --pilean-faint: var(--bp-color-text-faint, #7b8190);
  --pilean-rule: var(--bp-color-border-panel, #d9dce3);
  --pilean-surface: var(--bp-color-surface-muted, #f6f7f9);
  --pilean-focus: #1d4ed8;
}
html[data-theme="dark"] { --pilean-focus: #7cb4ff; }
@media (prefers-color-scheme: dark) {
  html:not([data-theme="light"]) { --pilean-focus: #7cb4ff; }
}
.pilean-figure {
  margin: 1.75rem 0;
  padding: 0;
  max-width: 100%;
}
.pilean-figure-frame {
  display: flex;
  justify-content: center;
  max-width: 100%;
}
.pilean-figure-img {
  display: block;
  max-width: 100%;
  height: auto;
  border-radius: 6px;
}
.pilean-figure-motion { display: block; max-width: 100%; }
.pilean-figure-stack { position: relative; display: inline-block; max-width: 100%; }
.pilean-backdrop-img {
  display: block;
  width: 100%;
  max-width: 100%;
  height: auto;
  border-radius: 6px;
}
.pilean-figure-over { position: absolute; inset: 0; pointer-events: none; }
.pilean-figure-over .pilean-figure-img {
  width: 100%;
  height: 100%;
  max-width: none;
  border-radius: 6px;
}
.pilean-figure-dark { display: none; }
html[data-theme="dark"] .pilean-figure-has-dark .pilean-figure-light { display: none; }
html[data-theme="dark"] .pilean-figure-has-dark .pilean-figure-dark { display: block; }
@media (prefers-color-scheme: dark) {
  html:not([data-theme="light"]) .pilean-figure-has-dark .pilean-figure-light { display: none; }
  html:not([data-theme="light"]) .pilean-figure-has-dark .pilean-figure-dark { display: block; }
}
.pilean-figure-caption {
  margin: 0.7rem auto 0;
  max-width: 44rem;
  font-size: 0.95em;
  line-height: 1.5;
  text-align: center;
  overflow-wrap: anywhere;
}
.pilean-figure-caption p { display: inline; margin: 0; }
.pilean-figure-number { font-weight: 600; margin-right: 0.45em; }
.pilean-figure-source {
  display: flex;
  flex-wrap: wrap;
  justify-content: center;
  gap: 0.25rem 1.1rem;
  margin-top: 0.45rem;
  font-size: 0.82em;
  color: var(--pilean-muted);
}
.pilean-source-item {
  display: inline-flex;
  flex-wrap: wrap;
  justify-content: center;
  align-items: baseline;
  gap: 0.35em;
  min-width: 0;
  max-width: 100%;
}
.pilean-source-key {
  font-size: 0.85em;
  letter-spacing: 0.04em;
  text-transform: uppercase;
  color: var(--pilean-faint);
}
.pilean-figure-source code, .pilean-figure-index code {
  font-size: 0.95em;
  overflow-wrap: anywhere;
}
.pilean-lean-link { display: none; }
html[data-lean-links] .pilean-lean-link { display: inline; }
html[data-lean-links] .pilean-lean-text { display: none; }
.pilean-repo-link, .pilean-lean-link { color: inherit; text-underline-offset: 0.15em; }
.pilean-fingerprint {
  display: inline-block;
  max-width: 12ch;
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
  vertical-align: bottom;
  cursor: text;
}
.pilean-fingerprint:hover, .pilean-fingerprint:focus { max-width: 100%; white-space: normal; }
.pilean-figure-missing { color: var(--pilean-muted); font-style: italic; }
.pilean-figure-index-intro { max-width: 44rem; }
.pilean-figure-index {
  list-style: none;
  margin: 1.5rem 0;
  padding: 0;
  display: grid;
  grid-template-columns: minmax(0, 1fr);
  gap: 1rem;
  overflow-wrap: anywhere;
}
.pilean-figure-index > li {
  display: grid;
  grid-template-columns: 9rem minmax(0, 1fr);
  gap: 0.4rem 1.2rem;
  padding: 1rem;
  border: 1px solid var(--pilean-rule);
  border-radius: 8px;
  background: var(--pilean-surface);
}
.pilean-index-thumb img {
  display: block;
  width: 100%;
  height: auto;
  border-radius: 4px;
}
.pilean-index-stack { position: relative; display: block; }
.pilean-index-over { position: absolute; inset: 0; }
.pilean-index-over img { width: 100%; height: 100%; }
.pilean-index-body { min-width: 0; }
.pilean-index-title { margin: 0 0 0.35rem; font-weight: 600; }
.pilean-index-facts {
  display: grid;
  grid-template-columns: max-content minmax(0, 1fr);
  gap: 0.2rem 0.9rem;
  margin: 0;
  font-size: 0.88em;
}
.pilean-index-facts dt { color: var(--pilean-faint); }
.pilean-index-facts dd { margin: 0; min-width: 0; overflow-wrap: anywhere; }
.pilean-index-files a { margin-right: 0.7em; }
@media (max-width: 600px) {
  .pilean-figure-index > li { grid-template-columns: minmax(0, 1fr); }
  .pilean-index-thumb { max-width: 14rem; }
  .pilean-index-facts { grid-template-columns: minmax(0, 1fr); }
  .pilean-index-facts dd { margin-bottom: 0.3rem; }
}
@media print {
  .pilean-figure-dark { display: none !important; }
  .pilean-figure-light { display: block !important; }
}
"##

/-- The stylesheet of a figure's page (`PILeanVersoManual.Page`). The columns of a motion's grid of
stills take their least width from `--pilean-still-col`, which `PILeanVerso.stillColumnCss` sets
from the list's classes (`PILeanVerso.stillColumnClasses`). -/
def pageCss : String := r##"
.pilean-figure-page { max-width: 100%; overflow-wrap: anywhere; }
.pilean-figure-page-anchor, .pilean-figure-page-anchor:target {
  position: absolute; width: 0; height: 0; overflow: hidden; scroll-margin-top: 12rem;
  margin: 0 !important; padding: 0 !important; border: 0 !important; outline: none !important;
  background: none !important; box-shadow: none !important; animation: none !important;
}
.pilean-figure-page li, .pilean-figure-page summary {
  font-family: var(--verso-text-font-family, inherit); line-height: 1.45;
}
.pilean-page-picture { margin: 1rem 0 0.5rem; }
.pilean-page-picture .pilean-figure-img { max-width: 100%; height: auto; }
.pilean-page-h { font-size: 1.15em; margin: 1.6rem 0 0.5rem; }
.pilean-page-files, .pilean-page-uses, .pilean-page-more-list, .pilean-page-external-list,
.pilean-page-prov-files {
  margin: 0.3rem 0; padding-left: 1.2rem;
}
.pilean-page-files li, .pilean-page-uses li { margin: 0.15rem 0; }
.pilean-page-download, .pilean-page-use { display: inline-block; min-height: 24px; }
.pilean-page-number { font-weight: 600; margin: 1rem 0 0.2rem; }
.pilean-page-caption-text { margin: 0 0 0.6rem; max-width: 44rem; }
.pilean-page-standing { border-left: 3px solid var(--pilean-rule); padding-left: 0.9rem; }
.pilean-standing-words { font-weight: 600; }
.pilean-standing-scope, .pilean-page-note, .pilean-page-via, .pilean-page-axioms,
.pilean-page-cut { color: var(--pilean-muted); font-size: 0.92em; max-width: 44rem; }
.pilean-page-decl { margin: 0.9rem 0 1.2rem; min-width: 0; }
.pilean-page-decl-title { font-size: 1em; margin: 0 0 0.35rem; font-weight: 600; }
.pilean-page-decl-title .pilean-repo-link, .pilean-page-decl-title .pilean-place {
  font-weight: normal; font-size: 0.88em; color: var(--pilean-muted);
}
.pilean-page-kind {
  font-size: 0.78em; letter-spacing: 0.04em; text-transform: uppercase;
  color: var(--pilean-faint); font-weight: normal;
}
.pilean-page-code, .pilean-page-plain {
  max-width: 100%; overflow-x: auto; border: 1px solid var(--pilean-rule);
  border-radius: 6px; background: var(--pilean-surface); padding: 0.6rem 0.8rem; margin: 0;
}
.pilean-page-code pre, .pilean-page-code .hl.lean.block { margin: 0; white-space: pre; }
.pilean-page-plain code { white-space: pre; }
.pilean-page-module { color: var(--pilean-faint); font-size: 0.88em; }
.pilean-page-more summary { cursor: pointer; min-height: 24px; }
.pilean-page-code-fold > summary {
  cursor: pointer; min-height: 24px; padding: 0.2rem 0; font-weight: 600;
}
.pilean-figure-page summary:focus-visible {
  outline: 3px solid var(--pilean-focus, #2563eb); outline-offset: 2px; border-radius: 3px;
}
.pilean-page-facts {
  display: grid; grid-template-columns: max-content minmax(0, 1fr); gap: 0.2rem 0.9rem;
  margin: 0.4rem 0; font-size: 0.9em;
}
.pilean-page-facts dt { color: var(--pilean-faint); }
.pilean-page-facts dd { margin: 0; min-width: 0; overflow-wrap: anywhere; }
.pilean-page-facts code { overflow-wrap: anywhere; word-break: break-all; }
.pilean-page-prov-file { margin: 0.6rem 0; }
@media (max-width: 600px) {
  .pilean-page-facts { grid-template-columns: minmax(0, 1fr); }
  .pilean-page-facts dd { margin-bottom: 0.3rem; }
}
.pilean-motion-words { max-width: 44rem; }
.pilean-motion-unchecked { border-left: 3px solid var(--pilean-rule); padding-left: 0.6rem; }
.pilean-motion-steps-wrap { max-width: 100%; overflow-x: auto; margin: 0.5rem 0 1rem; }
.pilean-motion-steps { border-collapse: collapse; font-size: 0.92em; }
.pilean-motion-steps caption {
  caption-side: top; text-align: left; color: var(--pilean-muted); padding-bottom: 0.3rem;
}
.pilean-motion-steps th, .pilean-motion-steps td {
  border-bottom: 1px solid var(--pilean-rule); padding: 0.3rem 0.7rem 0.3rem 0;
  text-align: left; vertical-align: top;
}
.pilean-motion-steps tbody th { font-weight: normal; white-space: nowrap; }
.pilean-motion-moves { margin: 0; padding-left: 1rem; }
.pilean-motion-crossfade { font-style: italic; }
.pilean-motion-panel { font-weight: 600; }
.pilean-page-motion-keys {
  list-style: none; margin: 0.5rem 0 1rem; padding: 0; display: grid;
  grid-template-columns: repeat(auto-fit, minmax(min(var(--pilean-still-col), 100%), 1fr));
  gap: 0.75rem; align-items: start;
}
.pilean-page-motion-key { margin: 0; min-width: 0; text-align: center; }
.pilean-page-motion-key img {
  display: block; max-width: 100%; height: auto; margin: 0 auto; border-radius: 4px;
}
"##

end PILeanVerso
