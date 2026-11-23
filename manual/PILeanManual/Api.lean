/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILeanManual.ApiMeta
import PILeanManual.ApiCoverage
import PILeanManual.Api.PILean
import PILeanManual.Api.PILean.Anim
import PILeanManual.Api.PILean.Anim.Animation
import PILeanManual.Api.PILean.Anim.Apng
import PILeanManual.Api.PILean.Anim.ApngRead
import PILeanManual.Api.PILean.Anim.Compose
import PILeanManual.Api.PILean.Anim.Frames
import PILeanManual.Api.PILean.Anim.Gif
import PILeanManual.Api.PILean.Anim.GifRead
import PILeanManual.Api.PILean.Anim.Lzw
import PILeanManual.Api.PILean.Anim.Proofs
import PILeanManual.Api.PILean.Anim.Quantize
import PILeanManual.Api.PILean.Canvas
import PILeanManual.Api.PILean.CheckLevel
import PILeanManual.Api.PILean.Color
import PILeanManual.Api.PILean.Diagram.Basic
import PILeanManual.Api.PILean.Diagram.Graph
import PILeanManual.Api.PILean.Diagram.Hasse
import PILeanManual.Api.PILean.Diagram.Path
import PILeanManual.Api.PILean.Diagram.Perm
import PILeanManual.Api.PILean.Diagram.SetSystem
import PILeanManual.Api.PILean.Diagram.Tree
import PILeanManual.Api.PILean.Diagram.Young
import PILeanManual.Api.PILean.Exact
import PILeanManual.Api.PILean.Exact.Algebraic
import PILeanManual.Api.PILean.Exact.Plane
import PILeanManual.Api.PILean.Exact.Spec
import PILeanManual.Api.PILean.Explorer
import PILeanManual.Api.PILean.Geometry
import PILeanManual.Api.PILean.Graph.Bundle
import PILeanManual.Api.PILean.Graph.Channel
import PILeanManual.Api.PILean.Graph.Check
import PILeanManual.Api.PILean.Graph.Compound
import PILeanManual.Api.PILean.Graph.Coordinates
import PILeanManual.Api.PILean.Graph.Dot
import PILeanManual.Api.PILean.Graph.Draw
import PILeanManual.Api.PILean.Graph.Fixed
import PILeanManual.Api.PILean.Graph.Layered
import PILeanManual.Api.PILean.Graph.Layering
import PILeanManual.Api.PILean.Graph.Layout
import PILeanManual.Api.PILean.Graph.Model
import PILeanManual.Api.PILean.Graph.Nested
import PILeanManual.Api.PILean.Graph.Ordering
import PILeanManual.Api.PILean.Graph.Pack
import PILeanManual.Api.PILean.Graph.Proofs
import PILeanManual.Api.PILean.Graph.Route
import PILeanManual.Api.PILean.Graph.Simple
import PILeanManual.Api.PILean.Graph.Simplex
import PILeanManual.Api.PILean.Graph.Spec
import PILeanManual.Api.PILean.Graph.Web
import PILeanManual.Api.PILean.Image.Basic
import PILeanManual.Api.PILean.Image.Ops
import PILeanManual.Api.PILean.Image.Proofs
import PILeanManual.Api.PILean.Path
import PILeanManual.Api.PILean.Plane
import PILeanManual.Api.PILean.Plane.Basic
import PILeanManual.Api.PILean.Plane.Check
import PILeanManual.Api.PILean.Plane.Draw
import PILeanManual.Api.PILean.Plane.Frame
import PILeanManual.Api.PILean.Plane.Graph
import PILeanManual.Api.PILean.Plane.Render
import PILeanManual.Api.PILean.Plot.Check
import PILeanManual.Api.PILean.Plot.Exact
import PILeanManual.Api.PILean.Plot.Figure
import PILeanManual.Api.PILean.Plot.Proofs
import PILeanManual.Api.PILean.Plot.Sample
import PILeanManual.Api.PILean.Plot.Scale
import PILeanManual.Api.PILean.Plot.Ticks
import PILeanManual.Api.PILean.Png
import PILeanManual.Api.PILean.Png.Checksum
import PILeanManual.Api.PILean.Png.Deflate
import PILeanManual.Api.PILean.Png.Inflate
import PILeanManual.Api.PILean.Png.Proofs
import PILeanManual.Api.PILean.Png.Read
import PILeanManual.Api.PILean.Png.Tables
import PILeanManual.Api.PILean.Png.Types
import PILeanManual.Api.PILean.Png.Write
import PILeanManual.Api.PILean.Raster.Blur
import PILeanManual.Api.PILean.Raster.Canvas
import PILeanManual.Api.PILean.Raster.Coverage
import PILeanManual.Api.PILean.Raster.Draw
import PILeanManual.Api.PILean.Raster.Proofs
import PILeanManual.Api.PILean.Raster.SrgbTables
import PILeanManual.Api.PILean.Raster.Stroke
import PILeanManual.Api.PILean.Raster.SvgRender
import PILeanManual.Api.PILean.Sort
import PILeanManual.Api.PILean.Style
import PILeanManual.Api.PILean.Svg
import PILeanManual.Api.PILean.Svg.Inert
import PILeanManual.Api.PILean.Text.Engine
import PILeanManual.Api.PILean.Text.Lettering
import PILeanManual.Api.PILean.Text.LetteringArrows
import PILeanManual.Api.PILean.Text.LetteringCompose
import PILeanManual.Api.PILean.Text.LetteringGlyphs
import PILeanManual.Api.PILean.Text.LetteringGreek
import PILeanManual.Api.PILean.Text.LetteringLatin
import PILeanManual.Api.PILean.Text.LetteringLower
import PILeanManual.Api.PILean.Text.LetteringMath
import PILeanManual.Api.PILean.Text.LetteringScripts
import PILeanManual.Api.PILean.Text.LetteringSymbols
import PILeanManual.Api.PILean.Text.LetteringTypo
import PILeanManual.Api.PILean.Trust.Attr
import PILeanManual.Api.PILean.Trust.Build
import PILeanManual.Api.PILean.Trust.Figure
import PILeanManual.Api.PILean.Trust.Files
import PILeanManual.Api.PILean.Trust.Fingerprint
import PILeanManual.Api.PILean.Trust.Json
import PILeanManual.Api.PILean.Trust.Manifest
import PILeanManual.Api.PILean.Trust.Provenance
import PILeanManual.Api.PILean.Trust.Renderer
import PILeanManual.Api.PILean.Trust.Sha256
import PILeanManual.Api.PILean.Trust.Sha256Proofs
import PILeanManual.Api.PILean.Trust.Verify
import PILeanManual.Api.PILean.Version

-- Written by `lake exe pilean-manual-pages`; `lake test` fails when it is stale.

open Verso.Genre Manual
open PILeanManual

#doc (Manual) "API Reference" =>
%%%
tag := "api"
%%%

One page for every module of the core, made from the library's docstrings when the
manual is built: each page opens with the module's documentation and lists its public
declarations in source order (what counts as public: {ref "api-coverage"}[What the Reference Covers]).

The modules, by the folder they are in:

* *PILean*:
  {ref "api-PILean"}[`PILean`],
  {ref "api-PILean.Canvas"}[`PILean.Canvas`],
  {ref "api-PILean.CheckLevel"}[`PILean.CheckLevel`],
  {ref "api-PILean.Color"}[`PILean.Color`],
  {ref "api-PILean.Explorer"}[`PILean.Explorer`],
  {ref "api-PILean.Geometry"}[`PILean.Geometry`],
  {ref "api-PILean.Path"}[`PILean.Path`],
  {ref "api-PILean.Sort"}[`PILean.Sort`],
  {ref "api-PILean.Style"}[`PILean.Style`],
  {ref "api-PILean.Version"}[`PILean.Version`]
* *Anim*:
  {ref "api-PILean.Anim"}[`PILean.Anim`],
  {ref "api-PILean.Anim.Animation"}[`PILean.Anim.Animation`],
  {ref "api-PILean.Anim.Apng"}[`PILean.Anim.Apng`],
  {ref "api-PILean.Anim.ApngRead"}[`PILean.Anim.ApngRead`],
  {ref "api-PILean.Anim.Compose"}[`PILean.Anim.Compose`],
  {ref "api-PILean.Anim.Frames"}[`PILean.Anim.Frames`],
  {ref "api-PILean.Anim.Gif"}[`PILean.Anim.Gif`],
  {ref "api-PILean.Anim.GifRead"}[`PILean.Anim.GifRead`],
  {ref "api-PILean.Anim.Lzw"}[`PILean.Anim.Lzw`],
  {ref "api-PILean.Anim.Proofs"}[`PILean.Anim.Proofs`],
  {ref "api-PILean.Anim.Quantize"}[`PILean.Anim.Quantize`]
* *Diagram*:
  {ref "api-PILean.Diagram.Basic"}[`PILean.Diagram.Basic`],
  {ref "api-PILean.Diagram.Graph"}[`PILean.Diagram.Graph`],
  {ref "api-PILean.Diagram.Hasse"}[`PILean.Diagram.Hasse`],
  {ref "api-PILean.Diagram.Path"}[`PILean.Diagram.Path`],
  {ref "api-PILean.Diagram.Perm"}[`PILean.Diagram.Perm`],
  {ref "api-PILean.Diagram.SetSystem"}[`PILean.Diagram.SetSystem`],
  {ref "api-PILean.Diagram.Tree"}[`PILean.Diagram.Tree`],
  {ref "api-PILean.Diagram.Young"}[`PILean.Diagram.Young`]
* *Exact*:
  {ref "api-PILean.Exact"}[`PILean.Exact`],
  {ref "api-PILean.Exact.Algebraic"}[`PILean.Exact.Algebraic`],
  {ref "api-PILean.Exact.Plane"}[`PILean.Exact.Plane`],
  {ref "api-PILean.Exact.Spec"}[`PILean.Exact.Spec`]
* *Graph*:
  {ref "api-PILean.Graph.Bundle"}[`PILean.Graph.Bundle`],
  {ref "api-PILean.Graph.Channel"}[`PILean.Graph.Channel`],
  {ref "api-PILean.Graph.Check"}[`PILean.Graph.Check`],
  {ref "api-PILean.Graph.Compound"}[`PILean.Graph.Compound`],
  {ref "api-PILean.Graph.Coordinates"}[`PILean.Graph.Coordinates`],
  {ref "api-PILean.Graph.Dot"}[`PILean.Graph.Dot`],
  {ref "api-PILean.Graph.Draw"}[`PILean.Graph.Draw`],
  {ref "api-PILean.Graph.Fixed"}[`PILean.Graph.Fixed`],
  {ref "api-PILean.Graph.Layered"}[`PILean.Graph.Layered`],
  {ref "api-PILean.Graph.Layering"}[`PILean.Graph.Layering`],
  {ref "api-PILean.Graph.Layout"}[`PILean.Graph.Layout`],
  {ref "api-PILean.Graph.Model"}[`PILean.Graph.Model`],
  {ref "api-PILean.Graph.Nested"}[`PILean.Graph.Nested`],
  {ref "api-PILean.Graph.Ordering"}[`PILean.Graph.Ordering`],
  {ref "api-PILean.Graph.Pack"}[`PILean.Graph.Pack`],
  {ref "api-PILean.Graph.Proofs"}[`PILean.Graph.Proofs`],
  {ref "api-PILean.Graph.Route"}[`PILean.Graph.Route`],
  {ref "api-PILean.Graph.Simple"}[`PILean.Graph.Simple`],
  {ref "api-PILean.Graph.Simplex"}[`PILean.Graph.Simplex`],
  {ref "api-PILean.Graph.Spec"}[`PILean.Graph.Spec`],
  {ref "api-PILean.Graph.Web"}[`PILean.Graph.Web`]
* *Image*:
  {ref "api-PILean.Image.Basic"}[`PILean.Image.Basic`],
  {ref "api-PILean.Image.Ops"}[`PILean.Image.Ops`],
  {ref "api-PILean.Image.Proofs"}[`PILean.Image.Proofs`]
* *Plane*:
  {ref "api-PILean.Plane"}[`PILean.Plane`],
  {ref "api-PILean.Plane.Basic"}[`PILean.Plane.Basic`],
  {ref "api-PILean.Plane.Check"}[`PILean.Plane.Check`],
  {ref "api-PILean.Plane.Draw"}[`PILean.Plane.Draw`],
  {ref "api-PILean.Plane.Frame"}[`PILean.Plane.Frame`],
  {ref "api-PILean.Plane.Graph"}[`PILean.Plane.Graph`],
  {ref "api-PILean.Plane.Render"}[`PILean.Plane.Render`]
* *Plot*:
  {ref "api-PILean.Plot.Check"}[`PILean.Plot.Check`],
  {ref "api-PILean.Plot.Exact"}[`PILean.Plot.Exact`],
  {ref "api-PILean.Plot.Figure"}[`PILean.Plot.Figure`],
  {ref "api-PILean.Plot.Proofs"}[`PILean.Plot.Proofs`],
  {ref "api-PILean.Plot.Sample"}[`PILean.Plot.Sample`],
  {ref "api-PILean.Plot.Scale"}[`PILean.Plot.Scale`],
  {ref "api-PILean.Plot.Ticks"}[`PILean.Plot.Ticks`]
* *Png*:
  {ref "api-PILean.Png"}[`PILean.Png`],
  {ref "api-PILean.Png.Checksum"}[`PILean.Png.Checksum`],
  {ref "api-PILean.Png.Deflate"}[`PILean.Png.Deflate`],
  {ref "api-PILean.Png.Inflate"}[`PILean.Png.Inflate`],
  {ref "api-PILean.Png.Proofs"}[`PILean.Png.Proofs`],
  {ref "api-PILean.Png.Read"}[`PILean.Png.Read`],
  {ref "api-PILean.Png.Tables"}[`PILean.Png.Tables`],
  {ref "api-PILean.Png.Types"}[`PILean.Png.Types`],
  {ref "api-PILean.Png.Write"}[`PILean.Png.Write`]
* *Raster*:
  {ref "api-PILean.Raster.Blur"}[`PILean.Raster.Blur`],
  {ref "api-PILean.Raster.Canvas"}[`PILean.Raster.Canvas`],
  {ref "api-PILean.Raster.Coverage"}[`PILean.Raster.Coverage`],
  {ref "api-PILean.Raster.Draw"}[`PILean.Raster.Draw`],
  {ref "api-PILean.Raster.Proofs"}[`PILean.Raster.Proofs`],
  {ref "api-PILean.Raster.SrgbTables"}[`PILean.Raster.SrgbTables`],
  {ref "api-PILean.Raster.Stroke"}[`PILean.Raster.Stroke`],
  {ref "api-PILean.Raster.SvgRender"}[`PILean.Raster.SvgRender`]
* *Svg*:
  {ref "api-PILean.Svg"}[`PILean.Svg`],
  {ref "api-PILean.Svg.Inert"}[`PILean.Svg.Inert`]
* *Text*:
  {ref "api-PILean.Text.Engine"}[`PILean.Text.Engine`],
  {ref "api-PILean.Text.Lettering"}[`PILean.Text.Lettering`],
  {ref "api-PILean.Text.LetteringArrows"}[`PILean.Text.LetteringArrows`],
  {ref "api-PILean.Text.LetteringCompose"}[`PILean.Text.LetteringCompose`],
  {ref "api-PILean.Text.LetteringGlyphs"}[`PILean.Text.LetteringGlyphs`],
  {ref "api-PILean.Text.LetteringGreek"}[`PILean.Text.LetteringGreek`],
  {ref "api-PILean.Text.LetteringLatin"}[`PILean.Text.LetteringLatin`],
  {ref "api-PILean.Text.LetteringLower"}[`PILean.Text.LetteringLower`],
  {ref "api-PILean.Text.LetteringMath"}[`PILean.Text.LetteringMath`],
  {ref "api-PILean.Text.LetteringScripts"}[`PILean.Text.LetteringScripts`],
  {ref "api-PILean.Text.LetteringSymbols"}[`PILean.Text.LetteringSymbols`],
  {ref "api-PILean.Text.LetteringTypo"}[`PILean.Text.LetteringTypo`]
* *Trust*:
  {ref "api-PILean.Trust.Attr"}[`PILean.Trust.Attr`],
  {ref "api-PILean.Trust.Build"}[`PILean.Trust.Build`],
  {ref "api-PILean.Trust.Figure"}[`PILean.Trust.Figure`],
  {ref "api-PILean.Trust.Files"}[`PILean.Trust.Files`],
  {ref "api-PILean.Trust.Fingerprint"}[`PILean.Trust.Fingerprint`],
  {ref "api-PILean.Trust.Json"}[`PILean.Trust.Json`],
  {ref "api-PILean.Trust.Manifest"}[`PILean.Trust.Manifest`],
  {ref "api-PILean.Trust.Provenance"}[`PILean.Trust.Provenance`],
  {ref "api-PILean.Trust.Renderer"}[`PILean.Trust.Renderer`],
  {ref "api-PILean.Trust.Sha256"}[`PILean.Trust.Sha256`],
  {ref "api-PILean.Trust.Sha256Proofs"}[`PILean.Trust.Sha256Proofs`],
  {ref "api-PILean.Trust.Verify"}[`PILean.Trust.Verify`]

{include 1 PILeanManual.ApiCoverage}

{include 1 PILeanManual.Api.PILean}

{include 1 PILeanManual.Api.PILean.Anim}

{include 1 PILeanManual.Api.PILean.Anim.Animation}

{include 1 PILeanManual.Api.PILean.Anim.Apng}

{include 1 PILeanManual.Api.PILean.Anim.ApngRead}

{include 1 PILeanManual.Api.PILean.Anim.Compose}

{include 1 PILeanManual.Api.PILean.Anim.Frames}

{include 1 PILeanManual.Api.PILean.Anim.Gif}

{include 1 PILeanManual.Api.PILean.Anim.GifRead}

{include 1 PILeanManual.Api.PILean.Anim.Lzw}

{include 1 PILeanManual.Api.PILean.Anim.Proofs}

{include 1 PILeanManual.Api.PILean.Anim.Quantize}

{include 1 PILeanManual.Api.PILean.Canvas}

{include 1 PILeanManual.Api.PILean.CheckLevel}

{include 1 PILeanManual.Api.PILean.Color}

{include 1 PILeanManual.Api.PILean.Diagram.Basic}

{include 1 PILeanManual.Api.PILean.Diagram.Graph}

{include 1 PILeanManual.Api.PILean.Diagram.Hasse}

{include 1 PILeanManual.Api.PILean.Diagram.Path}

{include 1 PILeanManual.Api.PILean.Diagram.Perm}

{include 1 PILeanManual.Api.PILean.Diagram.SetSystem}

{include 1 PILeanManual.Api.PILean.Diagram.Tree}

{include 1 PILeanManual.Api.PILean.Diagram.Young}

{include 1 PILeanManual.Api.PILean.Exact}

{include 1 PILeanManual.Api.PILean.Exact.Algebraic}

{include 1 PILeanManual.Api.PILean.Exact.Plane}

{include 1 PILeanManual.Api.PILean.Exact.Spec}

{include 1 PILeanManual.Api.PILean.Explorer}

{include 1 PILeanManual.Api.PILean.Geometry}

{include 1 PILeanManual.Api.PILean.Graph.Bundle}

{include 1 PILeanManual.Api.PILean.Graph.Channel}

{include 1 PILeanManual.Api.PILean.Graph.Check}

{include 1 PILeanManual.Api.PILean.Graph.Compound}

{include 1 PILeanManual.Api.PILean.Graph.Coordinates}

{include 1 PILeanManual.Api.PILean.Graph.Dot}

{include 1 PILeanManual.Api.PILean.Graph.Draw}

{include 1 PILeanManual.Api.PILean.Graph.Fixed}

{include 1 PILeanManual.Api.PILean.Graph.Layered}

{include 1 PILeanManual.Api.PILean.Graph.Layering}

{include 1 PILeanManual.Api.PILean.Graph.Layout}

{include 1 PILeanManual.Api.PILean.Graph.Model}

{include 1 PILeanManual.Api.PILean.Graph.Nested}

{include 1 PILeanManual.Api.PILean.Graph.Ordering}

{include 1 PILeanManual.Api.PILean.Graph.Pack}

{include 1 PILeanManual.Api.PILean.Graph.Proofs}

{include 1 PILeanManual.Api.PILean.Graph.Route}

{include 1 PILeanManual.Api.PILean.Graph.Simple}

{include 1 PILeanManual.Api.PILean.Graph.Simplex}

{include 1 PILeanManual.Api.PILean.Graph.Spec}

{include 1 PILeanManual.Api.PILean.Graph.Web}

{include 1 PILeanManual.Api.PILean.Image.Basic}

{include 1 PILeanManual.Api.PILean.Image.Ops}

{include 1 PILeanManual.Api.PILean.Image.Proofs}

{include 1 PILeanManual.Api.PILean.Path}

{include 1 PILeanManual.Api.PILean.Plane}

{include 1 PILeanManual.Api.PILean.Plane.Basic}

{include 1 PILeanManual.Api.PILean.Plane.Check}

{include 1 PILeanManual.Api.PILean.Plane.Draw}

{include 1 PILeanManual.Api.PILean.Plane.Frame}

{include 1 PILeanManual.Api.PILean.Plane.Graph}

{include 1 PILeanManual.Api.PILean.Plane.Render}

{include 1 PILeanManual.Api.PILean.Plot.Check}

{include 1 PILeanManual.Api.PILean.Plot.Exact}

{include 1 PILeanManual.Api.PILean.Plot.Figure}

{include 1 PILeanManual.Api.PILean.Plot.Proofs}

{include 1 PILeanManual.Api.PILean.Plot.Sample}

{include 1 PILeanManual.Api.PILean.Plot.Scale}

{include 1 PILeanManual.Api.PILean.Plot.Ticks}

{include 1 PILeanManual.Api.PILean.Png}

{include 1 PILeanManual.Api.PILean.Png.Checksum}

{include 1 PILeanManual.Api.PILean.Png.Deflate}

{include 1 PILeanManual.Api.PILean.Png.Inflate}

{include 1 PILeanManual.Api.PILean.Png.Proofs}

{include 1 PILeanManual.Api.PILean.Png.Read}

{include 1 PILeanManual.Api.PILean.Png.Tables}

{include 1 PILeanManual.Api.PILean.Png.Types}

{include 1 PILeanManual.Api.PILean.Png.Write}

{include 1 PILeanManual.Api.PILean.Raster.Blur}

{include 1 PILeanManual.Api.PILean.Raster.Canvas}

{include 1 PILeanManual.Api.PILean.Raster.Coverage}

{include 1 PILeanManual.Api.PILean.Raster.Draw}

{include 1 PILeanManual.Api.PILean.Raster.Proofs}

{include 1 PILeanManual.Api.PILean.Raster.SrgbTables}

{include 1 PILeanManual.Api.PILean.Raster.Stroke}

{include 1 PILeanManual.Api.PILean.Raster.SvgRender}

{include 1 PILeanManual.Api.PILean.Sort}

{include 1 PILeanManual.Api.PILean.Style}

{include 1 PILeanManual.Api.PILean.Svg}

{include 1 PILeanManual.Api.PILean.Svg.Inert}

{include 1 PILeanManual.Api.PILean.Text.Engine}

{include 1 PILeanManual.Api.PILean.Text.Lettering}

{include 1 PILeanManual.Api.PILean.Text.LetteringArrows}

{include 1 PILeanManual.Api.PILean.Text.LetteringCompose}

{include 1 PILeanManual.Api.PILean.Text.LetteringGlyphs}

{include 1 PILeanManual.Api.PILean.Text.LetteringGreek}

{include 1 PILeanManual.Api.PILean.Text.LetteringLatin}

{include 1 PILeanManual.Api.PILean.Text.LetteringLower}

{include 1 PILeanManual.Api.PILean.Text.LetteringMath}

{include 1 PILeanManual.Api.PILean.Text.LetteringScripts}

{include 1 PILeanManual.Api.PILean.Text.LetteringSymbols}

{include 1 PILeanManual.Api.PILean.Text.LetteringTypo}

{include 1 PILeanManual.Api.PILean.Trust.Attr}

{include 1 PILeanManual.Api.PILean.Trust.Build}

{include 1 PILeanManual.Api.PILean.Trust.Figure}

{include 1 PILeanManual.Api.PILean.Trust.Files}

{include 1 PILeanManual.Api.PILean.Trust.Fingerprint}

{include 1 PILeanManual.Api.PILean.Trust.Json}

{include 1 PILeanManual.Api.PILean.Trust.Manifest}

{include 1 PILeanManual.Api.PILean.Trust.Provenance}

{include 1 PILeanManual.Api.PILean.Trust.Renderer}

{include 1 PILeanManual.Api.PILean.Trust.Sha256}

{include 1 PILeanManual.Api.PILean.Trust.Sha256Proofs}

{include 1 PILeanManual.Api.PILean.Trust.Verify}

{include 1 PILeanManual.Api.PILean.Version}
