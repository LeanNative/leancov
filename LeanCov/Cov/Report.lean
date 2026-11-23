import Lean.Data.Json
import Std.Data.HashMap
import LeanCov.Cov.Types

/-! # Coverage, CRAP, Cognitive CRAP, JSON, and LCOV Reporter -/

namespace LeanCov.Cov
open Lean

structure FuncReport where
  name : String
  file : String
  line : Nat
  endLine : Nat
  lines : Nat
  cc : Nat
  cognitive : Nat
  sitesTotal : Nat
  sitesHit : Nat
  branchCov : Float
  crap : Float
  cogCrap : Float
  uncoveredLines : Array Nat := #[]
  deriving Repr, Inhabited, ToJson

structure FileReport where
  file : String
  functions : Nat
  functionsHit : Nat
  sitesTotal : Nat
  sitesHit : Nat
  branchCov : Float
  linesTotal : Nat
  linesHit : Nat
  lineCov : Float
  maxCrap : Float
  maxCogCrap : Float
  deriving Repr, Inhabited, ToJson

structure KindReport where
  kind : String
  total : Nat
  hit : Nat
  cov : Float
  deriving Repr, Inhabited, ToJson

structure SummaryReport where
  sitesTotal : Nat
  sitesHit : Nat
  branchCov : Float
  linesTotal : Nat
  linesHit : Nat
  lineCov : Float
  functionsTotal : Nat
  functionsHit : Nat
  maxCrap : Float
  maxCogCrap : Float
  avgCrap : Float
  avgCogCrap : Float
  crapOver30 : Nat
  cogCrapOver30 : Nat
  byKind : Array KindReport := #[]
  files : Array FileReport
  functions : Array FuncReport
  deriving Repr, Inhabited, ToJson

private def hitAt (hits : Array UInt64) (id : Nat) : UInt64 :=
  if h : id < hits.size then hits[id] else 0

private def pctRatio (num den : Nat) : Float :=
  if den == 0 then 1.0 else Float.ofNat num / Float.ofNat den

private def round1 (x : Float) : String :=
  let scaled := (x * 10.0 + 0.5).toUInt64.toNat
  s!"{scaled / 10}.{scaled % 10}"

private def padLeft (w : Nat) (s : String) : String :=
  if s.length >= w then s else String.ofList (List.replicate (w - s.length) ' ') ++ s

private def padRight (w : Nat) (s : String) : String :=
  if s.length >= w then s else s ++ String.ofList (List.replicate (w - s.length) ' ')

private def uniqueSortedNat (xs : Array Nat) : Array Nat := Id.run do
  let sorted := xs.qsort (· < ·)
  let mut out : Array Nat := #[]
  for x in sorted do
    if out.isEmpty || out[out.size - 1]! != x then
      out := out.push x
  return out

/-- Aggregate raw per-site hit counts against a `Manifest` into function, file, and total reports. -/
def buildReport (m : Manifest) (hits : Array UInt64) : SummaryReport := Id.run do
  -- Map siteId -> Site for fast lookup
  let mut siteById : Std.HashMap Nat Site := {}
  for s in m.sites do
    siteById := siteById.insert s.id s

  -- Per-function metrics
  let mut fnReports : Array FuncReport := Array.mkEmpty m.functions.size
  let mut fnsHit : Nat := 0
  let mut maxCrap : Float := 0.0
  let mut maxCogCrap : Float := 0.0
  let mut sumCrap : Float := 0.0
  let mut sumCogCrap : Float := 0.0
  let mut crapOver30 : Nat := 0
  let mut cogCrapOver30 : Nat := 0

  -- Group per-file accumulators
  let mut fileNames : Array String := #[]
  let mut fileSeen : Std.HashMap String Bool := {}
  for s in m.sites do
    if !fileSeen.contains s.file then
      fileSeen := fileSeen.insert s.file true
      fileNames := fileNames.push s.file
  for f in m.functions do
    if !fileSeen.contains f.file then
      fileSeen := fileSeen.insert f.file true
      fileNames := fileNames.push f.file
  fileNames := fileNames.qsort (· < ·)

  let mut fileSites : Std.HashMap String (Array Site) := {}
  for s in m.sites do
    let arr := (fileSites.getD s.file #[]).push s
    fileSites := fileSites.insert s.file arr

  let mut fileFns : Std.HashMap String (Array FuncReport) := {}

  for f in m.functions do
    let total := f.siteIds.size
    let mut covered : Nat := 0
    let mut missedLines : Array Nat := #[]
    for sid in f.siteIds do
      if hitAt hits sid > 0 then
        covered := covered + 1
      else if let some st := siteById.get? sid then
        missedLines := missedLines.push st.line
    let cov := pctRatio covered total
    let crap := crapScore f.cc cov
    let cogCrap := crapScore f.cognitive cov
    if covered > 0 then fnsHit := fnsHit + 1
    if crap > maxCrap then maxCrap := crap
    if cogCrap > maxCogCrap then maxCogCrap := cogCrap
    sumCrap := sumCrap + crap
    sumCogCrap := sumCogCrap + cogCrap
    if crap > 30.0 then crapOver30 := crapOver30 + 1
    if cogCrap > 30.0 then cogCrapOver30 := cogCrapOver30 + 1
    let fr : FuncReport := {
      name := f.name, file := f.file, line := f.line, endLine := f.endLine, lines := f.lines
      cc := f.cc, cognitive := f.cognitive
      sitesTotal := total, sitesHit := covered, branchCov := cov
      crap, cogCrap, uncoveredLines := uniqueSortedNat missedLines
    }
    fnReports := fnReports.push fr
    fileFns := fileFns.insert f.file ((fileFns.getD f.file #[]).push fr)

  let mut fileReports : Array FileReport := Array.mkEmpty fileNames.size
  let mut totSites : Nat := 0
  let mut totSitesHit : Nat := 0
  let mut totLines : Nat := 0
  let mut totLinesHit : Nat := 0

  for fn in fileNames do
    let ss := fileSites.getD fn #[]
    let fs := fileFns.getD fn #[]
    let mut brTot : Nat := 0
    let mut brHit : Nat := 0
    let mut lineHits : Std.HashMap Nat UInt64 := {}
    for s in ss do
      let c := hitAt hits s.id
      if s.kind.isBranch then
        brTot := brTot + 1
        if c > 0 then brHit := brHit + 1
      let prev := lineHits.getD s.line 0
      if c > prev then lineHits := lineHits.insert s.line c
      else if !lineHits.contains s.line then lineHits := lineHits.insert s.line 0
    let lTot := lineHits.size
    let mut lHit : Nat := 0
    for (_, c) in lineHits.toList do
      if c > 0 then lHit := lHit + 1
    let mut fHit : Nat := 0
    let mut fMaxCrap : Float := 0.0
    let mut fMaxCog : Float := 0.0
    for fr in fs do
      if fr.sitesHit > 0 then fHit := fHit + 1
      if fr.crap > fMaxCrap then fMaxCrap := fr.crap
      if fr.cogCrap > fMaxCog then fMaxCog := fr.cogCrap
    totSites := totSites + brTot
    totSitesHit := totSitesHit + brHit
    totLines := totLines + lTot
    totLinesHit := totLinesHit + lHit
    fileReports := fileReports.push {
      file := fn
      functions := fs.size, functionsHit := fHit
      sitesTotal := brTot, sitesHit := brHit, branchCov := pctRatio brHit brTot
      linesTotal := lTot, linesHit := lHit, lineCov := pctRatio lHit lTot
      maxCrap := fMaxCrap, maxCogCrap := fMaxCog
    }

  -- Per-BranchKind breakdown (shows happy-path vs error/boundary coverage at a glance)
  let mut kindTot : Std.HashMap String Nat := {}
  let mut kindHit : Std.HashMap String Nat := {}
  for s in m.sites do
    let k := s.kind.toString
    kindTot := kindTot.insert k (kindTot.getD k 0 + 1)
    if hitAt hits s.id > 0 then
      kindHit := kindHit.insert k (kindHit.getD k 0 + 1)
  let kindKeys := kindTot.toArray.qsort fun a b => a.1 < b.1
  let mut byKind : Array KindReport := Array.mkEmpty kindKeys.size
  for (k, tot) in kindKeys do
    let h := kindHit.getD k 0
    byKind := byKind.push { kind := k, total := tot, hit := h, cov := pctRatio h tot }

  let fnCount := fnReports.size
  let avgCrap := if fnCount == 0 then 0.0 else sumCrap / Float.ofNat fnCount
  let avgCogCrap := if fnCount == 0 then 0.0 else sumCogCrap / Float.ofNat fnCount
  return {
    sitesTotal := totSites, sitesHit := totSitesHit, branchCov := pctRatio totSitesHit totSites
    linesTotal := totLines, linesHit := totLinesHit, lineCov := pctRatio totLinesHit totLines
    functionsTotal := fnCount, functionsHit := fnsHit
    maxCrap, maxCogCrap, avgCrap, avgCogCrap
    crapOver30, cogCrapOver30
    byKind, files := fileReports, functions := fnReports
  }

/-- Export coverage data in standard LCOV `.info` format (compatible with `genhtml`, Codecov, VS Code). -/
def toLcov (m : Manifest) (hits : Array UInt64) : String := Id.run do
  let mut fileNames : Array String := #[]
  let mut seen : Std.HashMap String Bool := {}
  for s in m.sites do
    if !seen.contains s.file then seen := seen.insert s.file true; fileNames := fileNames.push s.file
  for f in m.functions do
    if !seen.contains f.file then seen := seen.insert f.file true; fileNames := fileNames.push f.file
  fileNames := fileNames.qsort (· < ·)

  let mut fileSites : Std.HashMap String (Array Site) := {}
  for s in m.sites do
    fileSites := fileSites.insert s.file ((fileSites.getD s.file #[]).push s)
  let mut fileFns : Std.HashMap String (Array FuncInfo) := {}
  for f in m.functions do
    fileFns := fileFns.insert f.file ((fileFns.getD f.file #[]).push f)

  let mut lines : Array String := #[]
  for file in fileNames do
    lines := lines.push "TN:"
    lines := lines.push s!"SF:{file}"
    let fns := (fileFns.getD file #[]).qsort fun a b => a.line < b.line
    for f in fns do
      lines := lines.push s!"FN:{f.line},{f.name}"
    let mut fnh : Nat := 0
    for f in fns do
      let mut mx : UInt64 := 0
      for sid in f.siteIds do
        let c := hitAt hits sid
        if c > mx then mx := c
      if mx > 0 then fnh := fnh + 1
      lines := lines.push s!"FNDA:{mx},{f.name}"
    lines := lines.push s!"FNF:{fns.size}"
    lines := lines.push s!"FNH:{fnh}"

    let ss := (fileSites.getD file #[]).qsort fun a b =>
      if a.line != b.line then a.line < b.line else if a.col != b.col then a.col < b.col else a.id < b.id
    let mut brf : Nat := 0
    let mut brh : Nat := 0
    let mut lineBranchIdx : Std.HashMap Nat Nat := {}
    let mut lineHits : Std.HashMap Nat UInt64 := {}
    for s in ss do
      let c := hitAt hits s.id
      if s.kind.isBranch then
        brf := brf + 1
        if c > 0 then brh := brh + 1
        let bIdx := lineBranchIdx.getD s.line 0
        lineBranchIdx := lineBranchIdx.insert s.line (bIdx + 1)
        lines := lines.push s!"BRDA:{s.line},0,{bIdx},{c}"
      let prev := lineHits.getD s.line 0
      if c > prev then lineHits := lineHits.insert s.line c
      else if !lineHits.contains s.line then lineHits := lineHits.insert s.line 0
    lines := lines.push s!"BRF:{brf}"
    lines := lines.push s!"BRH:{brh}"

    let sortedLines := lineHits.toArray.qsort fun a b => a.1 < b.1
    let mut lh : Nat := 0
    for (ln, c) in sortedLines do
      if c > 0 then lh := lh + 1
      lines := lines.push s!"DA:{ln},{c}"
    lines := lines.push s!"LF:{sortedLines.size}"
    lines := lines.push s!"LH:{lh}"
    lines := lines.push "end_of_record"
  return "\n".intercalate lines.toList ++ "\n"

inductive SortKey where
  | crap
  | cog
  | cc
  | uncov
  deriving BEq, Repr

def SortKey.toString : SortKey → String
  | .crap => "crap"
  | .cog => "cog"
  | .cc => "cc"
  | .uncov => "uncov"

def SortKey.ofString? : String → Option SortKey
  | "crap" => some .crap
  | "cog" | "cog-crap" | "cognitive" => some .cog
  | "cc" => some .cc
  | "uncov" | "missed" => some .uncov
  | _ => none

private def sortFuncReports (fns : Array FuncReport) (key : SortKey) : Array FuncReport :=
  fns.qsort fun a b =>
    match key with
    | .crap =>
      if a.crap != b.crap then a.crap > b.crap
      else if a.cogCrap != b.cogCrap then a.cogCrap > b.cogCrap
      else a.name < b.name
    | .cog =>
      if a.cogCrap != b.cogCrap then a.cogCrap > b.cogCrap
      else if a.crap != b.crap then a.crap > b.crap
      else a.name < b.name
    | .cc =>
      if a.cc != b.cc then a.cc > b.cc else a.cognitive > b.cognitive
    | .uncov =>
      let ua := a.sitesTotal - a.sitesHit
      let ub := b.sitesTotal - b.sitesHit
      if ua != ub then ua > ub else a.crap > b.crap

/-- Format a human-readable terminal summary of coverage, CRAP, and Cognitive CRAP. -/
def formatReport (r : SummaryReport) (topN : Nat := 25) (sortBy : SortKey := .crap)
    (showFiles : Bool := false) (showMissed : Bool := false) (showKinds : Bool := false) : String := Id.run do
  let mut out : Array String := #[]
  out := out.push "=== LeanCov Source-Level Coverage & CRAP ==="
  out := out.push s!"Branches:   {r.sitesHit}/{r.sitesTotal} ({round1 (r.branchCov * 100.0)}%)"
  out := out.push s!"Lines:      {r.linesHit}/{r.linesTotal} ({round1 (r.lineCov * 100.0)}%)"
  out := out.push s!"Functions:  {r.functionsHit}/{r.functionsTotal} ({round1 (pctRatio r.functionsHit r.functionsTotal * 100.0)}%)"
  out := out.push s!"McCabe CRAP:    max {round1 r.maxCrap} | avg {round1 r.avgCrap} | >30: {r.crapOver30}"
  out := out.push s!"Cognitive CRAP: max {round1 r.maxCogCrap} | avg {round1 r.avgCogCrap} | >30: {r.cogCrapOver30}"

  if showKinds && !r.byKind.isEmpty then
    out := out.push ""
    out := out.push "By branch kind:"
    out := out.push s!"  {padRight 14 "Kind"} {padLeft 11 "Hit/Tot"} {padLeft 7 "Cov"}"
    for kr in r.byKind do
      let ht := s!"{kr.hit}/{kr.total}"
      let cv := s!"{round1 (kr.cov * 100.0)}%"
      out := out.push s!"  {padRight 14 kr.kind} {padLeft 11 ht} {padLeft 7 cv}"

  if showFiles && !r.files.isEmpty then
    out := out.push ""
    out := out.push "By file:"
    out := out.push s!"  {padLeft 7 "BrCov"} {padLeft 10 "Hit/Tot"} {padLeft 7 "LnCov"} {padLeft 7 "MaxCRAP"} {padLeft 7 "MaxCog"}  File"
    let sortedFiles := r.files.qsort fun a b =>
      if a.maxCogCrap != b.maxCogCrap then a.maxCogCrap > b.maxCogCrap else a.file < b.file
    for fr in sortedFiles do
      let br := if fr.sitesTotal == 0 then "n/a" else s!"{round1 (fr.branchCov * 100.0)}%"
      let ln := if fr.linesTotal == 0 then "n/a" else s!"{round1 (fr.lineCov * 100.0)}%"
      let ht := s!"{fr.sitesHit}/{fr.sitesTotal}"
      out := out.push s!"  {padLeft 7 br} {padLeft 10 ht} {padLeft 7 ln} {padLeft 7 (round1 fr.maxCrap)} {padLeft 7 (round1 fr.maxCogCrap)}  {fr.file}"

  if topN > 0 && !r.functions.isEmpty then
    let sorted := sortFuncReports r.functions sortBy
    let shown := min topN sorted.size
    out := out.push ""
    out := out.push s!"Top {shown} functions (sorted by {sortBy.toString}):"
    out := out.push s!"  {padLeft 7 "CRAP"} {padLeft 7 "CogCRAP"} {padLeft 4 "CC"} {padLeft 4 "Cog"} {padLeft 7 "BrCov"} {padLeft 9 "Hit/Tot"}  Function"
    for i in [:shown] do
      let f := sorted[i]!
      let br := s!"{round1 (f.branchCov * 100.0)}%"
      let ht := s!"{f.sitesHit}/{f.sitesTotal}"
      let loc := s!"{f.file}:{f.line}"
      out := out.push s!"  {padLeft 7 (round1 f.crap)} {padLeft 7 (round1 f.cogCrap)} {padLeft 4 (toString f.cc)} {padLeft 4 (toString f.cognitive)} {padLeft 7 br} {padLeft 9 ht}  {f.name} ({loc})"
      if showMissed && !f.uncoveredLines.isEmpty then
        let lns := ", ".intercalate (f.uncoveredLines.toList.map toString)
        out := out.push s!"      missed lines: {lns}"
  return "\n".intercalate out.toList

/-- Format a static complexity report (without runtime coverage data). -/
def formatStaticAnalysis (m : Manifest) (topN : Nat := 30) (sortByCog : Bool := true) : String := Id.run do
  let mut out : Array String := #[]
  let mut maxCC : Nat := 0
  let mut maxCog : Nat := 0
  let mut ccOver15 : Nat := 0
  let mut cogOver15 : Nat := 0
  for f in m.functions do
    if f.cc > maxCC then maxCC := f.cc
    if f.cognitive > maxCog then maxCog := f.cognitive
    if f.cc > 15 then ccOver15 := ccOver15 + 1
    if f.cognitive > 15 then cogOver15 := cogOver15 + 1
  out := out.push "=== LeanCov Static Complexity Analysis ==="
  out := out.push s!"Declarations: {m.functions.size} | Probe sites: {m.sites.size} | Skipped files: {m.skippedFiles.size}"
  out := out.push s!"Max McCabe CC: {maxCC} (>15: {ccOver15}) | Max Cognitive: {maxCog} (>15: {cogOver15})"
  let sorted := m.functions.qsort fun a b =>
    if sortByCog then
      if a.cognitive != b.cognitive then a.cognitive > b.cognitive else a.cc > b.cc
    else
      if a.cc != b.cc then a.cc > b.cc else a.cognitive > b.cognitive
  let shown := min topN sorted.size
  if shown > 0 then
    out := out.push ""
    out := out.push s!"Top {shown} declarations:"
    out := out.push s!"  {padLeft 4 "Cog"} {padLeft 4 "CC"} {padLeft 6 "Sites"} {padLeft 5 "Lines"}  Function"
    for i in [:shown] do
      let f := sorted[i]!
      out := out.push s!"  {padLeft 4 (toString f.cognitive)} {padLeft 4 (toString f.cc)} {padLeft 6 (toString f.siteIds.size)} {padLeft 5 (toString f.lines)}  {f.name} ({f.file}:{f.line})"
  return "\n".intercalate out.toList

end LeanCov.Cov
