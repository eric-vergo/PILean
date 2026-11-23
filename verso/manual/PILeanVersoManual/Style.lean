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
The `lean:` links are shown only when the root has `data-lean-links` (a viewer that handles them
sets it); otherwise the declaration is plain code.
-/

namespace PILeanVerso

/-- The stylesheet of the figure blocks and the figures page. -/
def figureCss : String := r##"
:root {
  --pilean-muted: var(--bp-color-text-muted, #5b6170);
  --pilean-faint: var(--bp-color-text-faint, #7b8190);
  --pilean-rule: var(--bp-color-border-panel, #d9dce3);
  --pilean-surface: var(--bp-color-surface-muted, #f6f7f9);
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
  gap: 1rem;
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

end PILeanVerso
