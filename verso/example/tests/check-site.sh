#!/usr/bin/env bash
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
#
# Checks the example site end to end: it builds, its figures folder matches a fresh render and its
# manifest, every inline picture is the body of a file the manifest lists, two builds write the
# same bytes, the checks fail on damaged folders and pages, and the three link modes write the
# links they promise. It leaves the sites the browser check reads in SCRATCH: a (the default
# mode), site, none and sbs (side by side, links into the site).
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
desc="the figures page lists ten figures"
check test "$(grep -o 'class="pilean-index-title"' "$scratch/a/html-multi/Figures/index.html" | wc -l | tr -d ' ')" = 10
desc="no inline event handler and no script in the figures' markup"
check python3 -I tests/markup_check.py "$scratch/a/html-multi"
desc="every inline picture is the body of a file the manifest lists"
check python3 -I tests/inline_check.py "$scratch/a/html-multi"

# A page whose inline picture differs from its file.
rm -rf "$scratch/page"; cp -R "$scratch/a/html-multi" "$scratch/page"
explorers="$scratch/page/Pictures-with-proofs/Explorers/index.html"
python3 -I - "$explorers" <<'PY'
import sys
p = sys.argv[1]
s = open(p, encoding="utf-8").read()
i = s.index('id="inline-svg"')
j = s.index(' d="M', i)
open(p, "w", encoding="utf-8").write(s[:j] + ' d="M1 1 L2 2' + s[j + 5:])
PY
desc="the inline check refuses a page whose picture was changed"
check bash -c "python3 -I tests/inline_check.py '$scratch/page' | grep -q '#inline-svg: differs from'"
rm -rf "$scratch/page"

# A page whose theme rules were changed: a dark colour swapped, a declaration added.
tamper_theme() {
  rm -rf "$scratch/page"; cp -R "$scratch/a/html-multi" "$scratch/page"
  python3 -I - "$explorers" "$1" <<'PY'
import re, sys
p, how = sys.argv[1], sys.argv[2]
s = open(p, encoding="utf-8").read()
i = s.index('class="pilean-theme"', s.index('id="inline-svg"'))
j = s.index("</style>", i)
css = s[i:j]
if how == "colour":
    m = re.search(r"\{fill:(#[0-9a-f]{6})\}", css)
    other = "#000000" if m.group(1) != "#000000" else "#ffffff"
    css = css[:m.start(1)] + other + css[m.end(1):]
else:
    css += "svg path{opacity:0}"
open(p, "w", encoding="utf-8").write(s[:i] + css + s[j:])
PY
}
tamper_theme colour
desc="the inline check refuses a page whose theme rules have another dark colour"
check bash -c "python3 -I tests/inline_check.py '$scratch/page' | grep -q '#inline-svg: .*theme rules'"
tamper_theme rule
desc="the inline check refuses a page whose theme rules have a rule added"
check bash -c "python3 -I tests/inline_check.py '$scratch/page' | grep -q '#inline-svg: .*theme rules'"
rm -rf "$scratch/page"

# The link modes.
warns="$scratch/site-warnings.txt"
desc="the site builds with links into the site"
check bash -c "'$gen' --output '$scratch/site' --figure-lean-links site ${flags[*]} 2>'$warns' >/dev/null"
got=$(sed -n 's/^figures: warning: \(.*\) has no place in the site.*/\1/p' "$warns" | LC_ALL=C sort | tr '\n' '|')
want='Example.circleAnimation_spec|Example.collatzPlot_spec|Example.divisorGraph_spec|'
want+='Example.«odd "name" <a href=x> & '"'"'more'"'"'»|'
desc="it warns about exactly the declarations the site has no place for"; check test "$got" = "$want"
# Whether the markup of some figure of the site $1 matches the regular expression $2.
figures_have() {
  python3 -I - "$1" "$2" <<'PY'
import glob, re, sys
part = re.compile(r'<figure[^>]*class="pilean-figure.*?</figure>', re.S)
hits = [p for p in glob.glob(sys.argv[1] + "/**/index.html", recursive=True)
        for f in part.findall(open(p, encoding="utf-8").read()) if re.search(sys.argv[2], f)]
sys.exit(0 if hits else 1)
PY
}
figures_lack() { ! figures_have "$@"; }
desc="with links into the site, no figure has a lean: link"
check figures_lack "$scratch/site/html-multi" 'href="lean:'
desc="with links into the site, an inline element links to its Blueprint entry"
check grep -q 'href="Pictures-with-proofs/A-function/#--informal-external-decl-[0-9]*-Example___cubic" class="pilean-decl-link"' "$scratch/site/html-multi/Pictures-with-proofs/Explorers/index.html"
desc="the site builds without links"
check "$gen" --output "$scratch/none" --figure-lean-links none "${flags[@]}"
desc="without links, no figure links a declaration"
check figures_lack "$scratch/none/html-multi" 'class="pilean-(decl|site|lean)-link"'
desc="without links, the figures page links no declaration"
check bash -c "! grep -qE 'class=\"pilean-(site|lean)-link\"' '$scratch/none/html-multi/Figures/index.html'"
desc="in the default mode, figures have lean: links"
check figures_have "$scratch/a/html-multi" 'href="lean:decl/Example\.cubic" class="pilean-decl-link"'
desc="the side-by-side site builds with links into the site"
check bash -c "'$gen' --output '$scratch/sbs' --side-by-side --figure-lean-links site ${flags[*]} >/dev/null 2>&1"
desc="an unknown link mode is refused"
check bash -c "! '$gen' --output '$scratch/c' --figure-lean-links web >/dev/null 2>&1"

# A directive used on a declaration it cannot show.
cat > "$scratch/Misuse.lean" <<'LEAN'
import VersoManual
import PILeanVerso
import Example
open Verso.Genre Manual PILeanVerso
#doc (Manual) "A plot shown as an explorer" =>
:::figure_explorer Example.cubicPlot
A plot.
:::
LEAN
desc="figure_explorer on a plot is an error that names its type and what to use"
check bash -c "! '$lake' lean '$scratch/Misuse.lean' >'$scratch/misuse.log' 2>&1 &&
  grep -q 'Example.cubicPlot has the type PILean.Plot.Figure, not PILean.Explorer' '$scratch/misuse.log' &&
  grep -q 'use figure for a picture' '$scratch/misuse.log'"

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
