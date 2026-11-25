/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanVersoManual.Themes
import PILeanVersoManual.Table
import PILeanVersoManual.Render
import PILeanVersoManual.Style
import PILeanVersoManual.Common
import PILeanVersoManual.Block
import PILeanVersoManual.Index
import PILeanVersoManual.PageData
import PILeanVersoManual.PageMeta
import PILeanVersoManual.Highlight
import PILeanVersoManual.Page
import PILeanVersoManual.Wrapper
import PILeanVersoManual.Main
import PILeanVersoManual.SiteLinks

/-!
# PILean figures in Verso's Manual genre

`import PILeanVersoManual` and `open PILeanVerso.Manual` in a manual's chapters give the
directive `figure`, the role `figref` and the command `{figure_list}`; the manual's generator
wraps `manualMain` in `PILeanVerso.Manual.withFigures` with the table `site_figures%`.
-/
