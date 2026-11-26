/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILean
import PILean.Trust.Attr
import PILeanManual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open PILeanManual

#doc (Manual) "Builds, Fingerprints and Checks" =>
%%%
tag := "trust-build"
%%%

```lean -show
namespace PILeanManual.Builds
open PILean PILean.Trust
```

A project's figures are rendered by a build, never committed by hand. This chapter says how a
build finds them, what it writes, how the files are identified, and what the two checkers answer.
The full specification is `docs/TRUST.md`, from "Renderable figures" on.

# Renderable Figures
%%%
tag := "trust-outputs"
%%%

A type with an instance of {name}`PILean.Trust.ToOutputs` can be rendered to files: each
{name}`PILean.Trust.Output` has a file-name suffix, a {name}`PILean.Trust.Format` (SVG, PNG, APNG,
GIF or PDF), its bytes (computed only when asked for) and its *specification*, the bytes the
fingerprint covers.

:::table +header
*
  * Type
  * Outputs
*
  * {name}`PILean.Plot.Figure`
  * SVG; PNG; PDF
*
  * {name}`PILean.Graph` (default layered layout, light style, scale 1), or
    {name}`PILean.Trust.GraphFigure` (graph, layout options, style, PNG scale)
  * SVG; PNG; PDF
*
  * {name}`PILean.Animation`
  * animated SVG; APNG; GIF; poster frame (PNG and PDF, suffix `-poster`)
:::

The specification of an output is the SVG document that PILean's deterministic writer makes from
the figure's drawing, before any source information is added: for an SVG output the document
itself; for the PNG and the PDF of a figure or a graph the SVG with text drawn as shapes, which is
the drawing the PNG is rasterised from and the PDF is written from; for an animation's APNG and
GIF the animated SVG, which holds every frame. The specification covers what is drawn: the
sampled values of a function (the points the figure takes), data, colours, sizes, text and
layout. It does not cover the function's code, nor anything that does not change the drawing.
The rasteriser is not part of the specification; a change to its source text changes the fingerprint
through the renderer's identity (below), and nothing here
checks that it rasterises correctly.

# `@[figure]` and `figures%`
%%%
tag := "trust-attr"
%%%

{api}`PILean.Trust.Attr` is the only part of PILean that imports `Lean`. `@[figure]` on a
definition whose type has a `ToOutputs` instance records, in an environment extension exported
with the module, the module, the declaration, the file (the module's name with `/` for `.`, never
an absolute path), the line and column where the declaration starts (the start of its doc comment
when it has one), and the SHA-256 of the declaration's source text. The attribute is an error on a
type without an instance and on a private declaration.

The term `figures%` becomes, where it is used, an array of {name}`PILean.Trust.FigureEntry`: one
entry for every registered declaration of the environment, sorted by module and then by name. A
project's build driver is three lines:

```
import MyFigures
import PILean.Trust.Build
def main (args : List String) : IO UInt32 := PILean.Trust.buildMain figures% args
```

```lean (name := attrEx)
open PILean.Plot in
/-- A small plot for the example. -/
@[figure]
def tiny : Figure := { panels := #[{ series := #[.line "y" #[⟨0, 0⟩, ⟨1, 1⟩]] }] }

#eval ((figures% : Array FigureEntry).map fun e => (e.decl, e.file, e.line)).filter
  (·.1.startsWith "PILeanManual.Builds")
```

```leanResult attrEx
```

# The Fingerprint
%%%
tag := "trust-fingerprint"
%%%

{name}`PILean.Trust.fingerprint` is the lowercase hexadecimal SHA-256 of a byte string made of the
header `PILean fingerprint 2` and a line feed, then nine fields, each as its length in eight bytes
(big-endian) followed by its bytes: the module, the declaration, the file, the line, the column,
the library version ({name}`PILean.version`), the renderer, the SHA-256 of the declaration's
source text, and the specification.

The renderer is {name}`PILean.Trust.rendererId`: the SHA-256 of the Lean toolchain's version and of
the source text of every library module that turns a figure into bytes (plots, graphs, animations,
the SVG writer, the rasteriser, the lettering, the PNG, APNG, GIF and PDF writers, the source
records),
taken when the library was compiled. Any change to that code changes every fingerprint, even a
change to a comment. An output drawn with another text engine records that engine's identity, and
its renderer field is {name}`PILean.Trust.rendererWith` of it.

```lean (name := rendererEx)
#eval rendererId
#eval rendererSources.size
#eval (fingerprint "spec".toUTF8
  { module := "M", decl := "M.f", file := "M.lean", line := 1, column := 0,
    sourceHash := String.ofList (List.replicate 64 '0') }).length
```

```leanResult rendererEx
```

So changing the specification, the source text, the position, the library version or the
renderer changes the fingerprint. The repository and the commit are not part of it: the same
figure built at two commits has the same fingerprint if neither its drawing nor its declaration
(apart from the line) changed. The output formats of one animation share one fingerprint, because
they share the specification; each file's own SHA-256 is in the manifest.

# `pilean-build`
%%%
tag := "trust-pilean-build"
%%%

```
pilean-build [--out DIR] [--repo URL] [--commit SHA] [--check]
```

Without `--check`, every output of every entry is rendered, its source record (with the
fingerprint, and the repository and commit if given) is written into it, and the file goes to
`DIR/<module with / for .>/<declaration without the module prefix><suffix>.<extension>` (`--out`
defaults to `figures`), then `DIR/manifest.json`. The same entries, options and library give the
same bytes. Nothing is written if any figure fails to render; file names have only
`[A-Za-z0-9._-]`, and a path component that is empty, `.` or `..` is refused, so nothing is
written outside `DIR`. `--repo` must be an `http` or `https` link, `--commit` 4 to 64 lowercase
hexadecimal digits. At most 4096 figures and 65,536 files (the most a manifest may list), each
file at most 64 MiB with its source record in (the most `pilean-verify` reads a source record
from), checked on the finished file; a file whose bytes are not of its output's format is
refused, and so is an SVG that is not inert, so every file a build writes is one `pilean-verify`
can check.

With `--check`, the output is rendered in memory and compared byte for byte with `DIR`: it prints
`stale: PATH`, `missing: PATH` and `extra: PATH` for each difference, and `ok: N files match` if
there is none. The folder is listed to at most 32 levels of directories and 100,000 entries
(directories count, empty ones included); a folder beyond either bound gets the line `cannot check:
REASON` instead of a partial listing. Exit status 0 on success, 1 if a file is stale, missing or
extra, the folder cannot be listed completely or a figure cannot be rendered, 2 on a wrong command
line.

## The Manifest
%%%
tag := "trust-manifest"
%%%

`DIR/manifest.json` is one JSON object, `{"format":"pilean-manifest-4","files":[…]}`, with one
line per output, sorted by path: the path, the format, the size, the SHA-256 of the file's bytes,
the fingerprint recorded in it, the source record's fields, and the repository and commit when
the build was given them. The theorems of a linked figure are a JSON array of strings, so a name
written with `«` and `»` that holds a space or a quote is read back as it is. Every file of a
motion records it: the key `kind` is `motion`, `keys` the number of key frames, `cycle` the
length of one cycle in seconds, exactly (`n` or `n/d` in lowest terms), and `captions` the number
of captions; the files of one declaration must all record the same motion, and an entry with a
key this format does not have is refused. The readers also take the earlier formats,
`pilean-manifest-3` (before motions), `pilean-manifest-2` (one string of names separated by single
spaces) and `pilean-manifest-1` (the same under the key `proves`).

# `pilean-verify`
%%%
tag := "trust-verify"
%%%

```
lake exe pilean-verify DIR
```

reads `DIR/manifest.json` as untrusted input: a regular file (not a link, FIFO or device), at most
16 MiB, read by a small bounded JSON reader. The manifest is rejected as a whole, before any file
is touched, if a path is malformed (empty, absolute, with `..`, `.`, an empty component, a
backslash, a colon, or a character outside `[A-Za-z0-9._/-]`), listed twice, of an unknown format
or with a malformed hash. The folder is then listed, to at most 32 levels of directories and
100,000 entries; a folder beyond either bound is an error (exit status 1 and a message, no line
about any file), never a partial listing. Then each listed file gets one line, and after them
each file that is not listed:

:::table +header
*
  * Line
  * Meaning
*
  * `ok: PATH`
  * a regular file of the listed size, SHA-256 and format, whose source record agrees with the
    manifest
*
  * `missing: PATH`
  * no file has that path, spelled exactly so (on a file system that ignores case, a file found
    only under another spelling is `missing`, and `extra` under its own)
*
  * `changed: PATH`
  * another size or hash
*
  * `format differs: PATH`
  * the bytes are not of the listed format (`svg`, `png`, `apng` with an `acTL` chunk before the
    image data, `gif`)
*
  * `not inert: PATH`
  * an SVG file that is not inert (`PILean.Svg.isInert`), which no build writes
*
  * `not a regular file: PATH`
  * the file, or a directory on its way below `DIR`, is a symbolic link, a directory, a FIFO or a
    device (nothing is followed or opened)
*
  * `source differs: PATH`
  * the source record in the file differs from the manifest
*
  * `no source: PATH`
  * the file has no readable source record
*
  * `extra: PATH`
  * a file below `DIR` that the manifest does not list
:::

Every path and message printed goes through {name}`PILean.Trust.escapeControl`, so no line can
be forged or hidden by the manifest. Exit status 0 only if every line is `ok`; 1 otherwise, or if
the manifest is missing or invalid; 2 on a wrong command line. `pilean-verify` renders nothing.

# What the Answers Establish
%%%
tag := "trust-check"
%%%

In the words of `docs/TRUST.md`:

* `pilean-info` prints what a file says about itself. A source record is written by whoever
  wrote the file; nothing is signed, so the record alone establishes nothing.
* `pilean-verify` exiting 0 establishes that the directory and its manifest agree: every listed file
  is there under exactly its listed name, with the listed size, SHA-256 and format, and carries the
  listed source record, and there is no other file (a folder too deep or too large to list
  completely is an error, not a pass; directories that hold no file are not compared). It does not
  establish where either came from. Someone who can write both the files and the manifest can make a
  directory that passes, with any source record; the fingerprint is compared with the manifest's,
  not recomputed.
* `pilean-build --check` exiting 0 establishes that the directory holds, byte for byte, what the
  driver that was run renders now from the declarations compiled into it, and nothing else. That
  ties the files to the Lean source to the extent that the driver was built from that source by a
  toolchain you trust, on the checkout you mean. It is the only one of the three that looks at
  the Lean declarations.
* None of them says that a picture is correct: the fingerprint identifies a drawing and its
  declaration, and the theorems ({ref "proofs"}[What a Picture Proves]) are about the Lean object,
  not the pixels.
* The file checks are made with `lstat` before each open; a folder that another process changes
  during the check is outside what they defend against.

# Use in CI
%%%
tag := "trust-ci"
%%%

Either of two set-ups. *Build into the site*: CI runs the project's build driver and the site uses
the folder, which is not in version control. *Keep them committed and check them*: the folder is
in version control, written by the driver only, and CI runs `--check` with the same `--repo` and
`--commit` (or none, if the committed files were built without), which fails when a committed
file is not what the build produces (edited by hand, outdated, missing, or left over).

```
lake build
lake exe my-figures --out site/figures --repo "$REPO_URL" --commit "$(git rev-parse HEAD)"
lake exe pilean-verify site/figures        # the folder agrees with its manifest
# keeping the folder in version control instead:
lake exe my-figures --out figures --check   # fails on any stale, missing or extra file
```

This manual is built the first way: its generator renders the figures its pages use, writes them
with their records and a manifest, and fails if a file of that render is missing from the folder
it wrote or differs from it (a file left from an earlier build is reported, and fails the build
only with `--strict-figures`).
