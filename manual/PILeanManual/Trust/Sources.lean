/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILean
import PILeanManual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open PILeanManual

#doc (Manual) "Source Records" =>
%%%
tag := "trust-source"
%%%

```lean -show
namespace PILeanManual.Sources
open PILean PILean.Trust
```

An image can say which Lean declaration made it. PILean writes this *source record* into SVG,
PNG, APNG and GIF files and reads it back; `lake exe pilean-info FILE` prints it. The code is
{api}`PILean.Trust.Provenance`; the full specification of the encodings is `docs/TRUST.md`.

# The Record
%%%
tag := "trust-record"
%%%

A {name}`PILean.Trust.Source` holds the module, the declaration, the file (relative to the
repository), the line and column where the declaration starts, the version of PILean, and
optionally the repository's URL, the commit and a fingerprint (64 lowercase hexadecimal digits,
{ref "trust-fingerprint"}[The Fingerprint]). A record can be written only if every value is at most
4096 bytes of
UTF-8 and has only characters XML 1.0 can carry ({name}`PILean.Trust.Source.validate`).

* *SVG*: three elements, the first children of the root: a `title`, a `desc` and a `metadata`
  element holding one `pilean:source` element whose attributes are the fields.
* *PNG and APNG*: one uncompressed `iTXt` chunk per field (keyword `PILean:` and the key),
  directly after `IHDR`; the pixels and frames are not touched.
* *GIF*: one comment extension directly after the global colour table, its text the line
  `PILean source 1` and then `key=value` lines.

The writers of images are unchanged: an image without a record is byte for byte what it was (the
gallery's files are compared with a fresh render on every test run).
The record is added to a finished file ({name}`PILean.Trust.withSource`, which finds the format by
the file's signature) and read back by {name}`PILean.Trust.Source.read?`:

```lean (name := sourceEx)
def record : Source :=
  { module := "MyFigures", decl := "MyFigures.trig", file := "MyFigures.lean", line := 12,
    column := 0, version := PILean.version }

def svg : String := Svg.document 10 10 #[]

#eval (withSourceSvg svg record).map fun s => (s.splitOn "\n").take 4
#eval (withSourceSvg svg record).toOption.map fun s => infoLines s.toUTF8
#eval (withSourceSvg svg { record with decl := "bad\u0000name" }).toOption.isSome
```

```leanResult sourceEx
```

The last line is refused: NUL is a character XML cannot carry, and the readers refuse what the
writers refuse.

# Reading
%%%
tag := "trust-read"
%%%

{name}`PILean.Trust.Source.read?` treats every file as untrusted. The input must be at most
64 MiB ({name}`PILean.Trust.maxInput`) and each value at most 4096 bytes
({name}`PILean.Trust.maxField`); each key may occur once; unknown keys are ignored; the required
keys must be there. Nothing is executed or followed: a `repo` value is returned as text. The SVG
reader is a small bounded scanner, not a general XML parser; the PNG reader walks the chunks
before the first `IDAT` without decoding the image; the GIF reader walks the extensions before
the first image.

Two helpers for showing what was read: {name}`PILean.Trust.safeLink?` returns a URL only if it is
a plain `http` or `https` link of printable ASCII (so `javascript:`, `data:` and `file:` give
`none`), and {name}`PILean.Trust.escapeControl` writes control characters as escapes, for showing
untrusted text on one line.

```lean (name := linkEx)
#eval safeLink? "https://github.com/eric-vergo/PILean"
#eval safeLink? "javascript:alert(1)"
#eval escapeControl "line\nfeed\u001b[31m"
```

```leanResult linkEx
```

# `pilean-info`
%%%
tag := "trust-info"
%%%

```
lake exe pilean-info FILE
```

prints one `key: value` line per field ({name}`PILean.Trust.infoLines`), with control characters
escaped. Exit status 0 on success; 1, with a message on standard error, if the file cannot be
read, is larger than 64 MiB, or has no valid source record; 2 on a wrong command line.

# What a Record Establishes
%%%
tag := "trust-record-means"
%%%

A source record is written by whoever wrote the file; nothing is signed, so the record alone
establishes nothing. It says where to look. What ties a file to the Lean source is a build that
renders the declarations again and compares, and that only to the extent that the build was made
from that source by a toolchain you trust ({ref "trust-check"}[What the Answers Establish]).
