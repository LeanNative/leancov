import Lean.Data.Json
import Std.Data.HashMap
import LeanCov.Cov.Types

/-! # Coverage, CRAP, Cognitive CRAP, Diff, Patch Coverage, JSON, and LCOV Reporter -/

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
  deriving Repr, Inhabited, ToJson, FromJson

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
  deriving Repr, Inhabited, ToJson, FromJson

structure KindReport where
  kind : String
  total : Nat
  hit : Nat
  cov : Float
  deriving Repr, Inhabited, ToJson, FromJson

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
  deriving Repr, Inhabited, ToJson, FromJson

structure PatchReport where
  baseRef : String
  sitesTotal : Nat
  sitesHit : Nat
  branchCov : Float
  missed : Array Site := #[]
  deriving Repr, Inhabited, ToJson, FromJson

structure FuncDiff where
  name : String
  file : String
  line : Nat
  baseCov : Float
  headCov : Float
  covDelta : Float
  baseCrap : Float
  headCrap : Float
  crapDelta : Float
  baseCogCrap : Float
  headCogCrap : Float
  cogCrapDelta : Float
  deriving Repr, Inhabited, ToJson, FromJson

structure DiffReport where
  baseBranchCov : Float
  headBranchCov : Float
  branchCovDelta : Float
  baseLineCov : Float
  headLineCov : Float
  lineCovDelta : Float
  baseFuncCov : Float
  headFuncCov : Float
  funcCovDelta : Float
  baseMaxCrap : Float
  headMaxCrap : Float
  maxCrapDelta : Float
  baseMaxCogCrap : Float
  headMaxCogCrap : Float
  maxCogCrapDelta : Float
  regressed : Array FuncDiff := #[]
  improved : Array FuncDiff := #[]
  addedUncovered : Array FuncReport := #[]
  deriving Repr, Inhabited, ToJson, FromJson

private def hitAt (hits : Array UInt64) (id : Nat) : UInt64 :=
  if h : id < hits.size then hits[id] else 0

private def pctRatio (num den : Nat) : Float :=
  if den == 0 then 1.0 else Float.ofNat num / Float.ofNat den

private def round1 (x : Float) : String :=
  let nonNeg := if x < 0.0 then 0.0 else x
  let scaled := (nonNeg * 10.0 + 0.5).toUInt64.toNat
  s!"{scaled / 10}.{scaled % 10}"

private def fmtSigned1 (x : Float) : String :=
  if x < -0.05 then "-" ++ round1 (-x)
  else if x > 0.05 then "+" ++ round1 x
  else "0.0"

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

private def pathMatchesSuffix (a b : String) : Bool :=
  a == b || a.endsWith ("/" ++ b) || b.endsWith ("/" ++ a)

private def parseHunkPlusRange? (line : String) : Option (Nat × Nat) := do
  let afterOpen ← match line.splitOn "@@" with
    | _ :: hdr :: _ => some hdr.trimAscii.copy
    | _ => none
  let plusTok ← (afterOpen.splitOn " ").find? (·.startsWith "+")
  let body := (plusTok.drop 1).toString
  match body.splitOn "," with
  | [sStr] =>
    let start ← sStr.toNat?
    some (start, 1)
  | [sStr, cStr] =>
    let start ← sStr.toNat?
    let cnt ← cStr.toNat?
    some (start, cnt)
  | _ => none

/-- Parse `git diff -U0` unified diff text into a map from repo-relative file path to changed/added 1-based line numbers. -/
def parseGitUnifiedDiff (diffText : String) : Std.HashMap String (Array Nat) := Id.run do
  let mut out : Std.HashMap String (Array Nat) := {}
  let mut curFile : Option String := none
  for line in diffText.splitOn "\n" do
    if line.startsWith "diff --git " then
      curFile := none
    else if line.startsWith "+++ " then
      let raw := (line.drop 4).toString.trimAscii.copy
      if raw == "/dev/null" then
        curFile := none
      else if raw.startsWith "b/" then
        curFile := some (raw.drop 2).toString
      else
        curFile := some raw
    else if line.startsWith "@@ " then
      if let some f := curFile then
        if let some (start, cnt) := parseHunkPlusRange? line then
          if cnt > 0 then
            let mut arr := out.getD f #[]
            for i in [:cnt] do
              arr := arr.push (start + i)
            out := out.insert f arr
  return out

/-- Aggregate raw per-site hit counts against a `Manifest` into function, file, and total reports. -/
def buildReport (m : Manifest) (hits : Array UInt64) : SummaryReport := Id.run do
  let mut siteById : Std.HashMap Nat Site := {}
  for s in m.sites do
    siteById := siteById.insert s.id s

  let mut fnReports : Array FuncReport := Array.mkEmpty m.functions.size
  let mut fnsHit : Nat := 0
  let mut maxCrap : Float := 0.0
  let mut maxCogCrap : Float := 0.0
  let mut sumCrap : Float := 0.0
  let mut sumCogCrap : Float := 0.0
  let mut crapOver30 : Nat := 0
  let mut cogCrapOver30 : Nat := 0

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

/-- Evaluate coverage strictly on branch sites whose lines were added/modified in `changedLines`. -/
def buildPatchReport (m : Manifest) (hits : Array UInt64) (baseRef : String)
    (changedLines : Std.HashMap String (Array Nat)) : PatchReport := Id.run do
  let changedEntries : Array (String × Std.HashMap Nat Bool) :=
    changedLines.toArray.map fun (f, lns) =>
      let mp := lns.foldl (fun acc ln => acc.insert ln true) ({} : Std.HashMap Nat Bool)
      (f, mp)
  let mut tot : Nat := 0
  let mut hit : Nat := 0
  let mut missed : Array Site := #[]
  for s in m.sites do
    if s.kind.isBranch then
      let inDiff := changedEntries.any fun (df, lineMap) =>
        pathMatchesSuffix s.file df && lineMap.contains s.line
      if inDiff then
        tot := tot + 1
        if hitAt hits s.id > 0 then
          hit := hit + 1
        else
          missed := missed.push s
  return {
    baseRef
    sitesTotal := tot
    sitesHit := hit
    branchCov := pctRatio hit tot
    missed := missed.qsort fun a b =>
      if a.file != b.file then a.file < b.file
      else if a.line != b.line then a.line < b.line
      else a.col < b.col
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
  | cov
  deriving BEq, Repr

def SortKey.toString : SortKey → String
  | .crap => "crap"
  | .cog => "cog"
  | .cc => "cc"
  | .uncov => "uncov"
  | .cov => "cov"

def SortKey.ofString? : String → Option SortKey
  | "crap" => some .crap
  | "cog" | "cog-crap" | "cognitive" => some .cog
  | "cc" => some .cc
  | "uncov" | "missed" => some .uncov
  | "cov" | "low" => some .cov
  | _ => none

/-- Subset filters and kind exclusions applied prior to aggregating reports. -/
structure ReportFilter where
  files : Array String := #[]
  decls : Array String := #[]
  excludeKinds : Array BranchKind := #[]
  excludeInstances : Bool := false
  deriving Inhabited

def ReportFilter.isEmpty (flt : ReportFilter) : Bool :=
  flt.files.isEmpty && flt.decls.isEmpty && flt.excludeKinds.isEmpty && !flt.excludeInstances

private def matchesAnySubstr (pats : Array String) (s : String) : Bool :=
  pats.isEmpty || pats.any fun p => !p.isEmpty && (s.splitOn p).length > 1

/-- Filter manifest sites and functions without renumbering `Site.id`, preserving `.cov` counter alignment. -/
def filterManifest (m : Manifest) (flt : ReportFilter) : Manifest := Id.run do
  if flt.isEmpty then return m
  let mut instSiteIds : Std.HashMap Nat Bool := {}
  if flt.excludeInstances then
    for f in m.functions do
      if f.isInstance then
        for sid in f.siteIds do
          instSiteIds := instSiteIds.insert sid true
  let keptSites := m.sites.filter fun s =>
    !instSiteIds.contains s.id &&
    matchesAnySubstr flt.files s.file &&
    matchesAnySubstr flt.decls s.decl &&
    !flt.excludeKinds.contains s.kind
  let mut keptIds : Std.HashMap Nat Bool := {}
  for s in keptSites do
    keptIds := keptIds.insert s.id true
  let mut keptFns : Array FuncInfo := #[]
  for f in m.functions do
    if flt.excludeInstances && f.isInstance then
      continue
    if matchesAnySubstr flt.files f.file && matchesAnySubstr flt.decls f.name then
      let fSites := f.siteIds.filter keptIds.contains
      if !f.siteIds.isEmpty && fSites.isEmpty then
        continue
      keptFns := keptFns.push { f with siteIds := fSites }
  return { m with sites := keptSites, functions := keptFns }

/-- Sort function reports according to `key`. -/
def sortFuncReports (fns : Array FuncReport) (key : SortKey) : Array FuncReport :=
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
    | .cov =>
      if a.branchCov != b.branchCov then a.branchCov < b.branchCov
      else
        let ua := a.sitesTotal - a.sitesHit
        let ub := b.sitesTotal - b.sitesHit
        if ua != ub then ua > ub
        else if a.crap != b.crap then a.crap > b.crap
        else a.name < b.name

private def sortFileReports (files : Array FileReport) (sortBy : SortKey) : Array FileReport :=
  files.qsort fun a b =>
    if sortBy == .cov then
      let aEmpty := a.sitesTotal == 0
      let bEmpty := b.sitesTotal == 0
      if aEmpty != bEmpty then !aEmpty
      else if a.branchCov != b.branchCov then a.branchCov < b.branchCov
      else
        let ua := a.sitesTotal - a.sitesHit
        let ub := b.sitesTotal - b.sitesHit
        if ua != ub then ua > ub else a.file < b.file
    else
      if a.maxCogCrap != b.maxCogCrap then a.maxCogCrap > b.maxCogCrap else a.file < b.file

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
    let sortedFiles := sortFileReports r.files sortBy
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

/-- Format detailed uncovered sites (`file:line:col [kind]  <snippet>`) for a list of functions. -/
def formatMissedDetail (m : Manifest) (hits : Array UInt64) (fns : Array FuncReport)
    (srcRoot : System.FilePath) : IO String := do
  if fns.isEmpty then return ""
  let mut fileCache : Std.HashMap String (Array String) := {}
  let mut out : Array String := #[]
  for f in fns do
    let missed := (m.sites.filter fun s =>
      s.file == f.file && s.decl == f.name && hitAt hits s.id == 0).qsort fun a b =>
        if a.line != b.line then a.line < b.line else if a.col != b.col then a.col < b.col else a.id < b.id
    if missed.isEmpty then continue
    out := out.push s!"  {f.name} ({f.file}:{f.line}):"
    for s in missed do
      let srcLines ← match fileCache.get? s.file with
        | some ls => pure ls
        | none =>
          let ls ← try
            let raw ← IO.FS.readFile (srcRoot / s.file)
            pure (raw.splitOn "\n").toArray
          catch _ => pure #[]
          fileCache := fileCache.insert s.file ls
          pure ls
      let snip :=
        if s.line > 0 && s.line - 1 < srcLines.size then
          let t := srcLines[s.line - 1]!.trimAscii.copy
          let short := if t.length ≤ 96 then t else String.ofList (t.toList.take 93) ++ "..."
          if short.isEmpty then "" else s!"  {short}"
        else ""
      out := out.push s!"      missed: {s.file}:{s.line}:{s.col} [{s.kind.toString}]{snip}"
  if out.isEmpty then return ""
  return "Missed branch detail:\n" ++ "\n".intercalate out.toList

/-- Format the top `topN` most frequently executed sites using 64-bit counter magnitudes. -/
def formatHotSites (m : Manifest) (hits : Array UInt64) (topN : Nat := 20) : String := Id.run do
  let nonzero := m.sites.filterMap fun s =>
    let c := hitAt hits s.id
    if c > 0 then some (s, c) else none
  if nonzero.isEmpty || topN == 0 then
    return "Hottest sites: (no hits recorded)"
  let sorted := nonzero.qsort fun a b =>
    if a.2 != b.2 then a.2 > b.2 else a.1.id < b.1.id
  let shown := min topN sorted.size
  let mut out : Array String := #[]
  out := out.push s!"Hottest sites (top {shown}):"
  out := out.push s!"  {padLeft 12 "Hits"}  {padRight 14 "Kind"}  Location (Decl)"
  for i in [:shown] do
    let (s, c) := sorted[i]!
    out := out.push s!"  {padLeft 12 (toString c)}  {padRight 14 s.kind.toString}  {s.file}:{s.line}:{s.col} ({s.decl})"
  return "\n".intercalate out.toList

/-- Format a human-readable terminal patch-coverage summary. -/
def formatPatchReport (p : PatchReport) : String := Id.run do
  let mut out : Array String := #[]
  let pct := if p.sitesTotal == 0 then "n/a (0 changed branch sites)"
             else s!"{round1 (p.branchCov * 100.0)}% ({p.sitesHit}/{p.sitesTotal})"
  out := out.push s!"Patch coverage vs {p.baseRef}: {pct}"
  let shown := min 20 p.missed.size
  for i in [:shown] do
    let s := p.missed[i]!
    out := out.push s!"  missed patch branch: {s.file}:{s.line}:{s.col} [{s.kind.toString}] ({s.decl})"
  if p.missed.size > shown then
    out := out.push s!"  ... and {p.missed.size - shown} more missed patch branch(es)"
  return "\n".intercalate out.toList

/-- Format coverage summary, optional patch coverage, and top hotspots as GitHub-flavored Markdown. -/
def formatReportMarkdown (r : SummaryReport) (topN : Nat := 15) (sortBy : SortKey := .cog)
    (patch? : Option PatchReport := none) : String := Id.run do
  let mut out : Array String := #[]
  out := out.push "## LeanCov Report"
  out := out.push ""
  out := out.push "| Metric | Value |"
  out := out.push "|---|---:|"
  out := out.push s!"| Branches | {r.sitesHit}/{r.sitesTotal} ({round1 (r.branchCov * 100.0)}%) |"
  out := out.push s!"| Lines | {r.linesHit}/{r.linesTotal} ({round1 (r.lineCov * 100.0)}%) |"
  out := out.push s!"| Functions | {r.functionsHit}/{r.functionsTotal} ({round1 (pctRatio r.functionsHit r.functionsTotal * 100.0)}%) |"
  out := out.push s!"| McCabe CRAP | max {round1 r.maxCrap} (avg {round1 r.avgCrap}, >30: {r.crapOver30}) |"
  out := out.push s!"| Cognitive CRAP | max {round1 r.maxCogCrap} (avg {round1 r.avgCogCrap}, >30: {r.cogCrapOver30}) |"
  if let some p := patch? then
    let pct := if p.sitesTotal == 0 then "n/a" else s!"{p.sitesHit}/{p.sitesTotal} ({round1 (p.branchCov * 100.0)}%)"
    out := out.push s!"| Patch branches (`{p.baseRef}`) | {pct} |"
    if !p.missed.isEmpty then
      out := out.push ""
      out := out.push "### Missed Patch Branches"
      for i in [:min 15 p.missed.size] do
        let s := p.missed[i]!
        out := out.push s!"- `{s.file}:{s.line}:{s.col}` `[{s.kind.toString}]` (`{s.decl}`)"
  if topN > 0 && !r.functions.isEmpty then
    let sorted := sortFuncReports r.functions sortBy
    let shown := min topN sorted.size
    out := out.push ""
    out := out.push s!"### Top {shown} Functions (by `{sortBy.toString}`)"
    out := out.push ""
    out := out.push "| Function | Location | CRAP | CogCRAP | BrCov |"
    out := out.push "|---|---|---:|---:|---:|"
    for i in [:shown] do
      let f := sorted[i]!
      out := out.push s!"| `{f.name}` | `{f.file}:{f.line}` | {round1 f.crap} | {round1 f.cogCrap} | {round1 (f.branchCov * 100.0)}% |"
  return "\n".intercalate out.toList ++ "\n"

/-- Compute a structured regression/improvement diff between two `SummaryReport` snapshots. -/
def computeDiffReport (base head : SummaryReport) : DiffReport := Id.run do
  let mut baseMap : Std.HashMap (String × String) FuncReport := {}
  for f in base.functions do
    baseMap := baseMap.insert (f.file, f.name) f
  let mut regressed : Array FuncDiff := #[]
  let mut improved : Array FuncDiff := #[]
  let mut addedUncovered : Array FuncReport := #[]
  for f in head.functions do
    match baseMap.get? (f.file, f.name) with
    | some bf =>
      let fd : FuncDiff := {
        name := f.name, file := f.file, line := f.line
        baseCov := bf.branchCov, headCov := f.branchCov, covDelta := f.branchCov - bf.branchCov
        baseCrap := bf.crap, headCrap := f.crap, crapDelta := f.crap - bf.crap
        baseCogCrap := bf.cogCrap, headCogCrap := f.cogCrap, cogCrapDelta := f.cogCrap - bf.cogCrap
      }
      if fd.cogCrapDelta > 0.05 || fd.crapDelta > 0.05 then
        regressed := regressed.push fd
      else if fd.cogCrapDelta < -0.05 || fd.crapDelta < -0.05 then
        improved := improved.push fd
    | none =>
      if f.branchCov < 1.0 then
        addedUncovered := addedUncovered.push f
  let regSorted := regressed.qsort fun a b =>
    if a.cogCrapDelta != b.cogCrapDelta then a.cogCrapDelta > b.cogCrapDelta else a.crapDelta > b.crapDelta
  let impSorted := improved.qsort fun a b =>
    if a.cogCrapDelta != b.cogCrapDelta then a.cogCrapDelta < b.cogCrapDelta else a.crapDelta < b.crapDelta
  let addSorted := addedUncovered.qsort fun a b =>
    if a.cogCrap != b.cogCrap then a.cogCrap > b.cogCrap else a.name < b.name
  let baseFnCov := pctRatio base.functionsHit base.functionsTotal
  let headFnCov := pctRatio head.functionsHit head.functionsTotal
  return {
    baseBranchCov := base.branchCov, headBranchCov := head.branchCov
    branchCovDelta := head.branchCov - base.branchCov
    baseLineCov := base.lineCov, headLineCov := head.lineCov
    lineCovDelta := head.lineCov - base.lineCov
    baseFuncCov := baseFnCov, headFuncCov := headFnCov
    funcCovDelta := headFnCov - baseFnCov
    baseMaxCrap := base.maxCrap, headMaxCrap := head.maxCrap
    maxCrapDelta := head.maxCrap - base.maxCrap
    baseMaxCogCrap := base.maxCogCrap, headMaxCogCrap := head.maxCogCrap
    maxCogCrapDelta := head.maxCogCrap - base.maxCogCrap
    regressed := regSorted, improved := impSorted, addedUncovered := addSorted
  }

/-- Format a terminal diff report between two coverage snapshots. -/
def formatDiffReport (d : DiffReport) (topN : Nat := 15) : String := Id.run do
  let mut out : Array String := #[]
  out := out.push "=== LeanCov Coverage & CRAP Diff ==="
  out := out.push s!"Branches:       {round1 (d.baseBranchCov * 100.0)}% -> {round1 (d.headBranchCov * 100.0)}% ({fmtSigned1 (d.branchCovDelta * 100.0)}%)"
  out := out.push s!"Lines:          {round1 (d.baseLineCov * 100.0)}% -> {round1 (d.headLineCov * 100.0)}% ({fmtSigned1 (d.lineCovDelta * 100.0)}%)"
  out := out.push s!"Functions:      {round1 (d.baseFuncCov * 100.0)}% -> {round1 (d.headFuncCov * 100.0)}% ({fmtSigned1 (d.funcCovDelta * 100.0)}%)"
  out := out.push s!"Max CRAP:       {round1 d.baseMaxCrap} -> {round1 d.headMaxCrap} ({fmtSigned1 d.maxCrapDelta})"
  out := out.push s!"Max CogCRAP:    {round1 d.baseMaxCogCrap} -> {round1 d.headMaxCogCrap} ({fmtSigned1 d.maxCogCrapDelta})"
  if !d.regressed.isEmpty && topN > 0 then
    out := out.push ""
    out := out.push s!"Regressed functions ({d.regressed.size}):"
    for i in [:min topN d.regressed.size] do
      let f := d.regressed[i]!
      out := out.push s!"  +{padLeft 6 (round1 f.cogCrapDelta)} CogCRAP ({round1 f.baseCogCrap}->{round1 f.headCogCrap})  +{padLeft 6 (round1 f.crapDelta)} CRAP  {fmtSigned1 (f.covDelta * 100.0)}% cov  {f.name} ({f.file}:{f.line})"
  if !d.addedUncovered.isEmpty && topN > 0 then
    out := out.push ""
    out := out.push s!"Added uncovered functions ({d.addedUncovered.size}):"
    for i in [:min topN d.addedUncovered.size] do
      let f := d.addedUncovered[i]!
      out := out.push s!"  CogCRAP {round1 f.cogCrap}  cov {round1 (f.branchCov * 100.0)}%  {f.name} ({f.file}:{f.line})"
  if !d.improved.isEmpty && topN > 0 then
    out := out.push ""
    out := out.push s!"Improved functions ({d.improved.size}):"
    for i in [:min topN d.improved.size] do
      let f := d.improved[i]!
      out := out.push s!"  {fmtSigned1 f.cogCrapDelta} CogCRAP ({round1 f.baseCogCrap}->{round1 f.headCogCrap})  {fmtSigned1 (f.covDelta * 100.0)}% cov  {f.name} ({f.file}:{f.line})"
  return "\n".intercalate out.toList

/-- Format a `DiffReport` as GitHub-flavored Markdown. -/
def formatDiffMarkdown (d : DiffReport) (topN : Nat := 15) : String := Id.run do
  let mut out : Array String := #[]
  out := out.push "## LeanCov Diff Report"
  out := out.push ""
  out := out.push "| Metric | Base | Head | Delta |"
  out := out.push "|---|---:|---:|---:|"
  out := out.push s!"| Branches | {round1 (d.baseBranchCov * 100.0)}% | {round1 (d.headBranchCov * 100.0)}% | {fmtSigned1 (d.branchCovDelta * 100.0)}% |"
  out := out.push s!"| Lines | {round1 (d.baseLineCov * 100.0)}% | {round1 (d.headLineCov * 100.0)}% | {fmtSigned1 (d.lineCovDelta * 100.0)}% |"
  out := out.push s!"| Functions | {round1 (d.baseFuncCov * 100.0)}% | {round1 (d.headFuncCov * 100.0)}% | {fmtSigned1 (d.funcCovDelta * 100.0)}% |"
  out := out.push s!"| Max CRAP | {round1 d.baseMaxCrap} | {round1 d.headMaxCrap} | {fmtSigned1 d.maxCrapDelta} |"
  out := out.push s!"| Max CogCRAP | {round1 d.baseMaxCogCrap} | {round1 d.headMaxCogCrap} | {fmtSigned1 d.maxCogCrapDelta} |"
  if !d.regressed.isEmpty && topN > 0 then
    out := out.push ""
    out := out.push s!"### Regressed ({d.regressed.size})"
    out := out.push ""
    out := out.push "| Function | CogCRAP | Delta | Cov Delta |"
    out := out.push "|---|---:|---:|---:|"
    for i in [:min topN d.regressed.size] do
      let f := d.regressed[i]!
      out := out.push s!"| `{f.name}` (`{f.file}:{f.line}`) | {round1 f.headCogCrap} | {fmtSigned1 f.cogCrapDelta} | {fmtSigned1 (f.covDelta * 100.0)}% |"
  if !d.addedUncovered.isEmpty && topN > 0 then
    out := out.push ""
    out := out.push s!"### Added Uncovered ({d.addedUncovered.size})"
    for i in [:min topN d.addedUncovered.size] do
      let f := d.addedUncovered[i]!
      out := out.push s!"- `{f.name}` (`{f.file}:{f.line}`): CogCRAP {round1 f.cogCrap}, {round1 (f.branchCov * 100.0)}% branch cov"
  return "\n".intercalate out.toList ++ "\n"

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