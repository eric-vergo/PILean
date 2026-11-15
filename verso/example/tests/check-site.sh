#!/usr/bin/env bash
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
#
# Checks the example site end to end: it builds, its figures folder matches a fresh render and its
# manifest, two builds write the same bytes, and the checks fail on damaged folders.
#
#   tests/check-site.sh [SCRATCH]     (run from verso/example; LAKE names the lake to use)
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
cd "$here"
lake=${LAKE:-lake}
scratch=${1:-$(mktemp -d)}
mkdir -p "$scratch"
repo=https://github.com/eric-vergo/PILean
commit=0123456789abcdef0123456789abcdef01234567
flags=(--figure-repo "$repo" --figure-commit "$commit" --figure-source-prefix verso/example/
  --omit-build-time --omit-git-metadata --relative-source-paths)
gen=./.lake/build/bin/example-blueprint
fails=0
check() { if "$@"; then echo "ok: ${desc}"; else echo "FAIL: ${desc}"; fails=$((fails + 1)); fi; }

"$lake" build example-blueprint >/dev/null
(cd .. && cd .. && "$lake" build pilean-verify >/dev/null)
verify=../../.lake/build/bin/pilean-verify

desc="the adapter's checks hold (lake test)"; check "$lake" test
rm -rf "$scratch/a" "$scratch/b"
desc="the site builds"; check "$gen" --output "$scratch/a" "${flags[@]}"
figs="$scratch/a/html-multi/-verso-data/pilean-figures"
desc="the figures folder has its manifest"; check test -f "$figs/manifest.json"
desc="pilean-verify accepts the folder"; check "$verify" "$figs"
desc="--check-figures accepts the folder"; check "$gen" --check-figures "$figs" "${flags[@]}"
desc="the manifest records the repository and commit"; check grep -q "\"commit\":\"$commit\"" "$figs/manifest.json"

desc="a second build writes the same bytes"
"$gen" --output "$scratch/b" "${flags[@]}" >/dev/null
check diff -r -q "$scratch/a" "$scratch/b"

page="$scratch/a/html-multi/Pictures-with-proofs/A-function/index.html"
desc="the page has the figure with its number"; check grep -q 'Figure 1.1.1' "$page"
desc="the page links the source at the commit"
check grep -q "$repo/blob/$commit/verso/example/Example/Figures.lean#L" "$page"
desc="the page has the lean: link of the declaration"; check grep -q 'href="lean:decl/Example.cubicPlot"' "$page"
desc="the page names the theorem"; check grep -q 'lean:decl/Example.cubicPlot_spec' "$page"
desc="the page has a dark picture"; check grep -q 'Example.cubicPlot-dark.svg' "$page"
desc="the animation has its still frame for reduced motion"
check grep -q 'prefers-reduced-motion: reduce' "$scratch/a/html-multi/Pictures-with-proofs/Motion/index.html"
desc="the figures page lists four figures"
check test "$(grep -o 'class="pilean-index-title"' "$scratch/a/html-multi/Figures/index.html" | wc -l | tr -d ' ')" = 4
desc="no inline event handler and no script in the figures' markup"
check python3 -I tests/markup_check.py "$scratch/a/html-multi"

# Damaged copies.
cp -R "$figs" "$scratch/damaged"
svg=$(find "$scratch/damaged" -name '*.svg' | sort | head -n 1)
printf ' ' >> "$svg"
desc="--check-figures refuses a changed file"
check bash -c "! '$gen' --check-figures '$scratch/damaged' ${flags[*]} >/dev/null"
desc="pilean-verify refuses a changed file"; check bash -c "! '$verify' '$scratch/damaged' >/dev/null"
rm -rf "$scratch/damaged"; cp -R "$figs" "$scratch/damaged"
rm "$(find "$scratch/damaged" -name '*.png' | sort | head -n 1)"
desc="--check-figures refuses a missing file"
check bash -c "'$gen' --check-figures '$scratch/damaged' ${flags[*]} | grep -q '^missing: '"
rm -rf "$scratch/damaged"; cp -R "$figs" "$scratch/damaged"
touch "$scratch/damaged/left-over.svg"
desc="--check-figures reports an extra file"
check bash -c "'$gen' --check-figures '$scratch/damaged' ${flags[*]} | grep -q '^extra: left-over.svg'"
desc="--check-figures with another commit sees every file as stale"
check bash -c "'$gen' --check-figures '$figs' --figure-repo '$repo' --figure-commit abcd | grep -q '^stale: '"

# A file left in the output from an earlier build.
touch "$figs/left-over.svg"
desc="a left-over file is reported, the build passes"
check bash -c "'$gen' --output '$scratch/a' ${flags[*]} 2>&1 | grep -q 'extra: left-over.svg'"
desc="--strict-figures fails on a left-over file"
check bash -c "! '$gen' --output '$scratch/a' --strict-figures ${flags[*]} >/dev/null 2>&1"
rm "$figs/left-over.svg"
desc="a bad repository is refused"
check bash -c "! '$gen' --output '$scratch/c' --figure-repo 'javascript:x' >/dev/null 2>&1"

if [ "$fails" -eq 0 ]; then echo "check-site: all checks hold"; else echo "check-site: $fails failed"; exit 1; fi
