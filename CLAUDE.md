# PILean — project conventions

Pure Lean 4 imaging library (PIL/Pillow functional port). Zero dependencies, no FFI, no theorems.

## Build & test
- `lake build` — builds library + tests executable
- `lake exe tests` — run test suite; `lake exe tests --filter <substring>` to narrow
- `UPDATE_GOLDEN=1 lake exe tests` — (re)write golden fixtures under `tests/golden/`

## Project law (enforced in review)
- Coordinates are `Int` in public APIs and **clip silently** (drawing/geometry never fails). Sizes are `Nat`.
- `Rect` is half-open `[left,right) × [top,bottom)` everywhere.
- Pure codec code returns `Except DecodeError/EncodeError` — never panic on input data, no matter how malformed. `panic!` means "bug in PILean" only. `sorry` is banned.
- All pixel/byte data lives in `ByteArray` (never `Array Color`/`List` in hot paths).
- Image mutation routes through `Image.modifyData` (buffer-steal keeps refcount 1 so `ByteArray.set!` mutates in place). Never `{ img with data := img.data.set! ... }`.
- Hot loops: `Id.run do` + `let mut` + `for`/`while`; convert coordinates to `Nat`/`USize` once at the edge; no monad-transformer stacks per byte; `ByteArray.emptyWithCapacity` size hints.
- No array literals over ~1000 elements — embed blobs as hex strings decoded at init.
- Interface freeze: frozen public signatures (see git history of Wave 0) change only via the integrator. Adding new defs in your own module is always fine.
- Mathlib-style docstrings on every public def; `/-!` module headers.

## Layout
- `PILean/` library source (Core, Draw, Font, Transform, Filter, Binary, Compress, Codec, Color, IO)
- `Tests/` Lean test suites (one file per work package, registered in `Tests/Main.lean`)
- `tests/` fixtures: `golden/` (committed binaries), `corpus/` (vendored test corpora), `py/` (Pillow oracle scripts), `out/` (gitignored scratch output)
- Correctness oracle: Pillow 11.3.0 via `tests/py/` scripts; goldens are checked in, never regenerated in CI.
