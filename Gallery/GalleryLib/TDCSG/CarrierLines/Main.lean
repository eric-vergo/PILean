import GalleryLib.TDCSG.CarrierLines.Render

/-!
# Carrier-line plate entry point

Writes three PNGs and one proof/scene certificate beside each image.  The
certificate records the exact theorem driving the scene and a CRC-32 of the
raw RGB pixels.  A repository-side SHA-256 manifest can additionally bind the
encoded PNG and certificate files as a bundle.
-/

open PILean
open PILean.Compress
open Gallery.TDCSG.CarrierLines

def outDir : System.FilePath := System.FilePath.mk "out" / "tdcsg-carrier-lines"

def certificateHeader (name : String) (img : Image) : String :=
  s!"artifact: {name}\n\
dimensions: {img.width}x{img.height}\n\
pixel_mode: RGB\n\
raw_pixel_crc32_decimal: {crc32 img.data}\n\
exact_geometry_theorem: Gallery.TDCSG.CarrierLines.commonEdge_collinear\n\
theorem_assumption: cos(half polygon step) != 0\n\
raster_contract: exact scene geometry is deterministically rounded to PILean integer pixels\n\
"

def n10Certificate (img : Image) : String :=
  certificateHeader "n10-common-edge.png" img ++
  "claim_tier: proof-carrying render + paper theorem geometry\n" ++
  "order: 10\nphases_ccw: [3,6]\npolygon_scale: phi-1=1/phi\n" ++
  "carrier_lines: R*zeta and R*conj(zeta), angles +/-pi/5\n" ++
  "closed_carriers: {t*zeta^(+/-1) : -1/phi <= t <= 1/phi}\n" ++
  "disk_radius_squared: 4-phi\n" ++
  "endpoint_theorem: Gallery.TDCSG.CarrierLines.n10_carrierEndpoint_contact\n" ++
  "endpoint_fact: highlighted endpoints are exact cross-disk boundary contacts\n" ++
  "source_comparator: original TDCSG paper Figure 5(b), visual only for the unlabeled line motif\n"

def n20AtlasCertificate (img : Image) : String :=
  certificateHeader "n20-common-edge-atlas.png" img ++
  "claim_tier: proof-carrying render + retrospective finite-contact comparator\n" ++
  "order: 20\nphase_pairs_ccw: [(5,14),(6,13),(7,12),(8,11),(9,10)]\n" ++
  "line_angles: [+/-9,+/-27,+/-45,+/-63,+/-81] degrees\n" ++
  "scale_formula: s_j=-cos((2j+1)*pi/20)/cos(pi/20)>0\n" ++
  "disk_radius_squared: -8+6*t+7*t^2-4*t^3, t=2*cos(pi/10)\n" ++
  "scope_warning: retrospective finite-contact radius; no critical-radius or IET claim\n"

def n20FocusCertificate (img : Image) : String :=
  certificateHeader "n20-common-edge-focus-j09-j10.png" img ++
  "claim_tier: proof-carrying render + exact bounded-search annotation\n" ++
  "order: 20\nphases_ccw: [9,10]\npolygon_scale: 1\nline_angles: +/-81 degrees\n" ++
  "exact_edges: right [0,1+zeta^9] and [0,1+zeta^11], left by half-turn\n" ++
  "bounded_candidates: CE20-09=[Ab,Ba]; CE20-10=[aB,bA]\n" ++
  "scope_warning: carrier-meeting candidates only; not certified first returns or an IET\n" ++
  "exclusion: the separate 54-degree origin-ray experiment is not part of this common-edge scene\n"

def writeArtifact (filename : String) (img : Image) (cert : Image → String) : IO Unit := do
  let imagePath := outDir / filename
  img.save imagePath
  IO.FS.writeFile (outDir / (filename ++ ".certificate.txt")) (cert img)
  IO.println s!"wrote {imagePath} ({img.width}x{img.height}, raw CRC32={crc32 img.data})"

def main : IO Unit := do
  IO.FS.createDirAll outDir
  writeArtifact "n10-common-edge.png" n10Plate n10Certificate
  writeArtifact "n20-common-edge-atlas.png" n20AtlasPlate n20AtlasCertificate
  writeArtifact "n20-common-edge-focus-j09-j10.png" n20FocusPlate n20FocusCertificate
