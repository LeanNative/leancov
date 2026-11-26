import Std.Data.HashMap
import LeanCov.Cov.Types
import LeanCov.Cov.Report
import LeanCov.Cov.Mutate

/-! # Standalone HTML Coverage Report Generator -/

namespace LeanCov.Cov

/-- Escape HTML special characters in user source and identifiers. -/
def htmlEscape (s : String) : String :=
  ((((s.replace "&" "&amp;").replace "<" "&lt;").replace ">" "&gt;").replace "\"" "&quot;").replace "'" "&#39;"

/-- Map a relative Lean source path to a flat HTML filename inside `files/`. -/
def safeHtmlFileName (relFile : String) : String :=
  let clean := (((relFile.replace "/" "__").replace "\\" "__").replace ":" "__").replace " " "_"
  clean ++ ".html"

private def htmlPct (x : Float) : String :=
  let scaled := (x * 1000.0 + 0.5).toUInt64.toNat
  s!"{scaled / 10}.{scaled % 10}%"

private def htmlPctNum (x : Float) : Nat :=
  (x * 100.0 + 0.5).toUInt64.toNat

private def htmlScore (x : Float) : String :=
  let scaled := (x * 10.0 + 0.5).toUInt64.toNat
  s!"{scaled / 10}.{scaled % 10}"

private def htmlCovClass (cov : Float) : String :=
  if cov ≥ 0.8 then "ok" else if cov ≥ 0.5 then "warn" else "bad"

private def siteHitCount (hits : Array UInt64) (id : Nat) : UInt64 :=
  if h : id < hits.size then hits[id] else 0

private def htmlCss : String :=
":root { --bg:#0d1117; --fg:#e6edf3; --muted:#8b949e; --card:#161b22; --border:#30363d; --ok:#2ea043; --warn:#d29922; --bad:#f85149; --hitbg:rgba(46,160,67,.14); --partbg:rgba(210,153,34,.15); --missbg:rgba(248,81,73,.16); --link:#58a6ff; }
@media (prefers-color-scheme: light) { :root { --bg:#ffffff; --fg:#1f2328; --muted:#656d76; --card:#f6f8fa; --border:#d0d7de; --ok:#1a7f37; --warn:#9a6700; --bad:#cf222e; --hitbg:rgba(26,127,55,.10); --partbg:rgba(154,103,0,.12); --missbg:rgba(207,34,46,.12); --link:#0969da; } }
* { box-sizing:border-box; }
body { margin:0; padding:24px; font:14px/1.5 -apple-system,BlinkMacSystemFont,'Segoe UI',Helvetica,Arial,sans-serif; background:var(--bg); color:var(--fg); }
a { color:var(--link); text-decoration:none; } a:hover { text-decoration:underline; }
h1,h2 { margin:0 0 12px; } h2 { margin-top:28px; font-size:16px; }
.cards { display:grid; grid-template-columns:repeat(auto-fit,minmax(170px,1fr)); gap:12px; margin:16px 0; }
.card { background:var(--card); border:1px solid var(--border); border-radius:8px; padding:12px 14px; }
.card .lbl { color:var(--muted); font-size:12px; text-transform:uppercase; letter-spacing:.04em; }
.card .val { font-size:22px; font-weight:600; margin-top:4px; }
.ok { color:var(--ok); } .warn { color:var(--warn); } .bad { color:var(--bad); }
.search { width:100%; max-width:360px; padding:7px 10px; margin:8px 0 12px; border:1px solid var(--border); border-radius:6px; background:var(--card); color:var(--fg); }
table { width:100%; border-collapse:collapse; font-size:13px; }
th,td { text-align:left; padding:6px 10px; border-bottom:1px solid var(--border); }
th { background:var(--card); position:sticky; top:0; cursor:pointer; user-select:none; }
th.num, td.num { text-align:right; font-variant-numeric:tabular-nums; }
.bar { display:inline-block; width:72px; height:8px; background:var(--border); border-radius:4px; vertical-align:middle; margin-right:6px; overflow:hidden; }
.bar > span { display:block; height:100%; }
.bar .ok { background:var(--ok); } .bar .warn { background:var(--warn); } .bar .bad { background:var(--bad); }
.src-wrap { border:1px solid var(--border); border-radius:8px; overflow:auto; margin-top:12px; }
.src td { padding:1px 8px; border-bottom:none; font:12px/1.45 ui-monospace,SFMono-Regular,Menlo,Consolas,monospace; vertical-align:top; }
.src td.lnum { color:var(--muted); text-align:right; width:56px; user-select:none; border-right:1px solid var(--border); }
.src td.hits { color:var(--muted); text-align:right; width:64px; user-select:none; border-right:1px solid var(--border); }
.src td.code pre { margin:0; white-space:pre-wrap; word-break:break-word; display:inline; }
.ln-hit { background:var(--hitbg); } .ln-part { background:var(--partbg); } .ln-miss { background:var(--missbg); }
.ln-diff td.lnum { border-left:3px solid var(--link); }
.badge { display:inline-block; margin-left:6px; padding:0 5px; border-radius:4px; font-size:11px; border:1px solid var(--border); }
.b-hit { color:var(--ok); } .b-miss { color:var(--bad); font-weight:600; } .b-diff { color:var(--link); }
.controls { display:flex; gap:10px; align-items:center; flex-wrap:wrap; margin:8px 0 12px; }
select { padding:7px 10px; border:1px solid var(--border); border-radius:6px; background:var(--card); color:var(--fg); }
.fn-list { display:flex; flex-wrap:wrap; gap:6px; margin:10px 0 16px; }
.fn-pill { background:var(--card); border:1px solid var(--border); border-radius:999px; padding:2px 9px; font-size:12px; }
"

private def indexSortFilterJs : String :=
"<script>
(function(){
  var q = document.getElementById('file-filter');
  var tbl = document.getElementById('files-table');
  if (!tbl) return;
  if (q) q.addEventListener('input', function(){
    var v = q.value.toLowerCase();
    var rows = tbl.tBodies[0].rows;
    for (var i=0;i<rows.length;i++) {
      rows[i].style.display = rows[i].cells[0].textContent.toLowerCase().indexOf(v) >= 0 ? '' : 'none';
    }
  });
  var headers = tbl.tHead.rows[0].cells;
  for (var c=0;c<headers.length;c++) (function(col){
    var asc = false;
    headers[col].addEventListener('click', function(){
      asc = !asc;
      var tb = tbl.tBodies[0];
      var arr = Array.prototype.slice.call(tb.rows);
      arr.sort(function(a,b){
        var va = a.cells[col].getAttribute('data-v') || a.cells[col].textContent;
        var vb = b.cells[col].getAttribute('data-v') || b.cells[col].textContent;
        var na = parseFloat(va), nb = parseFloat(vb);
        var cmp = (!isNaN(na) && !isNaN(nb)) ? (na - nb) : va.localeCompare(vb);
        return asc ? cmp : -cmp;
      });
      arr.forEach(function(r){ tb.appendChild(r); });
    });
  })(c);
})();
</script>"

private def renderHtmlDoc (title body : String) : String :=
  s!"<!doctype html>\n<html lang=\"en\"><head><meta charset=\"utf-8\"><title>{htmlEscape title}</title><style>{htmlCss}</style></head>\n<body>\n{body}\n</body></html>\n"

private def renderIndexHtml (r : SummaryReport) (patch? : Option PatchReport := none) : String := Id.run do
  let fnCov := if r.functionsTotal == 0 then 1.0 else Float.ofNat r.functionsHit / Float.ofNat r.functionsTotal
  let mut parts : Array String := #[]
  parts := parts.push "<h1>LeanCov Coverage Report</h1>"
  parts := parts.push "<div class=\"cards\">"
  parts := parts.push s!"<div class=\"card\"><div class=\"lbl\">Branches</div><div class=\"val {htmlCovClass r.branchCov}\">{htmlPct r.branchCov}</div><div>{r.sitesHit}/{r.sitesTotal}</div></div>"
  parts := parts.push s!"<div class=\"card\"><div class=\"lbl\">Lines</div><div class=\"val {htmlCovClass r.lineCov}\">{htmlPct r.lineCov}</div><div>{r.linesHit}/{r.linesTotal}</div></div>"
  parts := parts.push s!"<div class=\"card\"><div class=\"lbl\">Functions</div><div class=\"val {htmlCovClass fnCov}\">{htmlPct fnCov}</div><div>{r.functionsHit}/{r.functionsTotal}</div></div>"
  parts := parts.push s!"<div class=\"card\"><div class=\"lbl\">Max CRAP</div><div class=\"val\">{htmlScore r.maxCrap}</div><div>avg {htmlScore r.avgCrap} (&gt;30: {r.crapOver30})</div></div>"
  parts := parts.push s!"<div class=\"card\"><div class=\"lbl\">Max CogCRAP</div><div class=\"val\">{htmlScore r.maxCogCrap}</div><div>avg {htmlScore r.avgCogCrap} (&gt;30: {r.cogCrapOver30})</div></div>"
  if let some pr := patch? then
    let pVal := if pr.sitesTotal == 0 then "n/a" else htmlPct pr.branchCov
    parts := parts.push s!"<div class=\"card\"><div class=\"lbl\">Patch ({htmlEscape pr.baseRef})</div><div class=\"val {htmlCovClass pr.branchCov}\">{pVal}</div><div>{pr.sitesHit}/{pr.sitesTotal}</div></div>"
  parts := parts.push "</div>"

  if !r.byKind.isEmpty then
    parts := parts.push "<h2>By Branch Kind</h2><table><thead><tr><th>Kind</th><th class=\"num\">Hit / Total</th><th class=\"num\">Coverage</th></tr></thead><tbody>"
    for kr in r.byKind do
      parts := parts.push s!"<tr><td><code>{htmlEscape kr.kind}</code></td><td class=\"num\">{kr.hit}/{kr.total}</td><td class=\"num {htmlCovClass kr.cov}\">{htmlPct kr.cov}</td></tr>"
    parts := parts.push "</tbody></table>"

  parts := parts.push "<h2>Files</h2>"
  parts := parts.push "<input id=\"file-filter\" class=\"search\" type=\"search\" placeholder=\"Filter files...\">"
  parts := parts.push "<table id=\"files-table\"><thead><tr><th>File</th><th class=\"num\">BrCov</th><th class=\"num\">Branches</th><th class=\"num\">LnCov</th><th class=\"num\">Funcs</th><th class=\"num\">MaxCRAP</th><th class=\"num\">MaxCogCRAP</th></tr></thead><tbody>"
  let sortedFiles := r.files.qsort fun a b =>
    if a.branchCov != b.branchCov then a.branchCov < b.branchCov else a.file < b.file
  for fr in sortedFiles do
    let link := "files/" ++ safeHtmlFileName fr.file
    let cls := htmlCovClass fr.branchCov
    let brBar := s!"<span class=\"bar\"><span class=\"{cls}\" style=\"width:{htmlPctNum fr.branchCov}%\"></span></span>{htmlPct fr.branchCov}"
    parts := parts.push s!"<tr><td><a href=\"{htmlEscape link}\">{htmlEscape fr.file}</a></td><td class=\"num\" data-v=\"{fr.branchCov}\">{brBar}</td><td class=\"num\" data-v=\"{fr.sitesTotal}\">{fr.sitesHit}/{fr.sitesTotal}</td><td class=\"num\" data-v=\"{fr.lineCov}\">{htmlPct fr.lineCov}</td><td class=\"num\" data-v=\"{fr.functions}\">{fr.functionsHit}/{fr.functions}</td><td class=\"num\">{htmlScore fr.maxCrap}</td><td class=\"num\">{htmlScore fr.maxCogCrap}</td></tr>"
  parts := parts.push "</tbody></table>"

  let topFns := (sortFuncReports r.functions .cog).take 50
  if !topFns.isEmpty then
    parts := parts.push "<h2>Top Functions (by CogCRAP)</h2><table><thead><tr><th>Function</th><th>Location</th><th class=\"num\">CRAP</th><th class=\"num\">CogCRAP</th><th class=\"num\">BrCov</th></tr></thead><tbody>"
    for f in topFns do
      let href := s!"files/{safeHtmlFileName f.file}#L{f.line}"
      parts := parts.push s!"<tr><td><code>{htmlEscape f.name}</code></td><td><a href=\"{htmlEscape href}\">{htmlEscape f.file}:{f.line}</a></td><td class=\"num\">{htmlScore f.crap}</td><td class=\"num\">{htmlScore f.cogCrap}</td><td class=\"num {htmlCovClass f.branchCov}\">{htmlPct f.branchCov}</td></tr>"
    parts := parts.push "</tbody></table>"

  parts := parts.push indexSortFilterJs
  return renderHtmlDoc "LeanCov Report" ("\n".intercalate parts.toList)

private def changedLineSet (file : String) (changedLines? : Option (Std.HashMap String (Array Nat))) :
    Std.HashMap Nat Bool := Id.run do
  let some mp := changedLines? | return {}
  let mut out : Std.HashMap Nat Bool := {}
  for (df, lns) in mp.toList do
    if pathMatchesSuffix file df then
      for ln in lns do
        out := out.insert ln true
  return out

private def renderSourcePage (fr : FileReport) (srcRoot : System.FilePath) (fileSites : Array Site)
    (fileFuncs : Array FuncReport) (hits : Array UInt64)
    (changedLines? : Option (Std.HashMap String (Array Nat)) := none) : IO String := do
  let diffLines := changedLineSet fr.file changedLines?
  let mut parts : Array String := #[]
  parts := parts.push "<p><a href=\"../index.html\">&larr; All Files</a></p>"
  parts := parts.push s!"<h1>{htmlEscape fr.file}</h1>"
  parts := parts.push "<div class=\"cards\">"
  parts := parts.push s!"<div class=\"card\"><div class=\"lbl\">Branches</div><div class=\"val {htmlCovClass fr.branchCov}\">{htmlPct fr.branchCov}</div><div>{fr.sitesHit}/{fr.sitesTotal}</div></div>"
  parts := parts.push s!"<div class=\"card\"><div class=\"lbl\">Lines</div><div class=\"val {htmlCovClass fr.lineCov}\">{htmlPct fr.lineCov}</div><div>{fr.linesHit}/{fr.linesTotal}</div></div>"
  parts := parts.push s!"<div class=\"card\"><div class=\"lbl\">Functions</div><div class=\"val\">{fr.functionsHit}/{fr.functions}</div></div>"
  parts := parts.push s!"<div class=\"card\"><div class=\"lbl\">Max CogCRAP</div><div class=\"val\">{htmlScore fr.maxCogCrap}</div><div>Max CRAP {htmlScore fr.maxCrap}</div></div>"
  parts := parts.push "</div>"

  let sortedFns := fileFuncs.qsort fun a b => a.line < b.line
  if !sortedFns.isEmpty then
    parts := parts.push "<div class=\"fn-list\">"
    for fn in sortedFns do
      parts := parts.push s!"<a class=\"fn-pill {htmlCovClass fn.branchCov}\" href=\"#L{fn.line}\">{htmlEscape fn.name} ({htmlPct fn.branchCov})</a>"
    parts := parts.push "</div>"

  let srcPath := srcRoot / fr.file
  let srcText? ← try
    let txt ← IO.FS.readFile srcPath
    pure (some txt)
  catch _ =>
    pure none

  match srcText? with
  | none =>
    parts := parts.push s!"<p class=\"bad\">Source file not found under <code>{htmlEscape srcRoot.toString}</code> (looked at <code>{htmlEscape srcPath.toString}</code>).</p>"
  | some raw =>
    let mut byLine : Std.HashMap Nat (Array Site) := {}
    let sortedSites := fileSites.qsort fun a b =>
      if a.line != b.line then a.line < b.line else if a.col != b.col then a.col < b.col else a.id < b.id
    for s in sortedSites do
      byLine := byLine.insert s.line ((byLine.getD s.line #[]).push s)
    let rawLines := (raw.splitOn "\n").toArray
    let lines := if rawLines.size > 1 && rawLines[rawLines.size - 1]! == "" then rawLines.pop else rawLines
    parts := parts.push "<div class=\"src-wrap\"><table class=\"src\"><tbody>"
    for idx in [:lines.size] do
      let ln := idx + 1
      let ss := byLine.getD ln #[]
      let (rowCls, hitsTxt) :=
        if ss.isEmpty then ("ln-none", "")
        else
          let allHit := ss.all fun s => siteHitCount hits s.id > 0
          let anyHit := ss.any fun s => siteHitCount hits s.id > 0
          let mx := ss.foldl (fun m s => max m (siteHitCount hits s.id)) 0
          let cls := if allHit then "ln-hit" else if anyHit then "ln-part" else "ln-miss"
          (cls, s!"{mx}x")
      let diffCls := if diffLines.contains ln then " ln-diff" else ""
      let mut badges := if diffLines.contains ln then "<span class=\"badge b-diff\">[diff]</span>" else ""
      for s in ss do
        let c := siteHitCount hits s.id
        let bCls := if c > 0 then "b-hit" else "b-miss"
        badges := badges ++ s!"<span class=\"badge {bCls}\">[{htmlEscape s.kind.toString} {c}]</span>"
      parts := parts.push s!"<tr id=\"L{ln}\" class=\"{rowCls}{diffCls}\"><td class=\"lnum\"><a href=\"#L{ln}\">{ln}</a></td><td class=\"hits\">{hitsTxt}</td><td class=\"code\"><pre>{htmlEscape lines[idx]!}</pre>{badges}</td></tr>"
    parts := parts.push "</tbody></table></div>"
  return renderHtmlDoc fr.file ("\n".intercalate parts.toList)

/-- Write a self-contained static HTML coverage site (`index.html` + `files/*.html`) to `outDir`. -/
def writeHtmlReport (outDir srcRoot : System.FilePath) (m : Manifest) (hits : Array UInt64)
    (rep : SummaryReport) (changedLines? : Option (Std.HashMap String (Array Nat)) := none)
    (patch? : Option PatchReport := none) : IO Unit := do
  let filesDir := outDir / "files"
  IO.FS.createDirAll filesDir
  IO.FS.writeFile (outDir / "index.html") (renderIndexHtml rep patch?)
  let mut sitesByFile : Std.HashMap String (Array Site) := {}
  for s in m.sites do
    sitesByFile := sitesByFile.insert s.file ((sitesByFile.getD s.file #[]).push s)
  let mut funcsByFile : Std.HashMap String (Array FuncReport) := {}
  for f in rep.functions do
    funcsByFile := funcsByFile.insert f.file ((funcsByFile.getD f.file #[]).push f)
  for fr in rep.files do
    let page ← renderSourcePage fr srcRoot (sitesByFile.getD fr.file #[]) (funcsByFile.getD fr.file #[]) hits changedLines?
    IO.FS.writeFile (filesDir / safeHtmlFileName fr.file) page

private def mutateFilterJs : String :=
"<script>
(function(){
  var q = document.getElementById('mut-q');
  var sel = document.getElementById('mut-out');
  var tbl = document.getElementById('mut-tbl');
  if (!tbl) return;
  function apply(){
    var v = q ? q.value.toLowerCase() : '';
    var o = sel ? sel.value : 'all';
    var rows = tbl.tBodies[0].rows;
    for (var i=0;i<rows.length;i++){
      var r = rows[i];
      var matchOut = (o === 'all') || (r.getAttribute('data-o') === o);
      var matchTxt = !v || r.textContent.toLowerCase().indexOf(v) >= 0;
      r.style.display = (matchOut && matchTxt) ? '' : 'none';
    }
  }
  if (q) q.addEventListener('input', apply);
  if (sel) sel.addEventListener('change', apply);
})();
</script>"

/-- Write a self-contained single-file HTML mutation report with live outcome filtering. -/
def writeMutateHtml (outFile : System.FilePath) (r : MutateReport) : IO Unit := do
  if let some p := outFile.parent then IO.FS.createDirAll p
  let scoreRatio := r.score / 100.0
  let mut parts : Array String := #[]
  parts := parts.push "<h1>LeanCov Mutation Report</h1>"
  parts := parts.push "<div class=\"cards\">"
  parts := parts.push s!"<div class=\"card\"><div class=\"lbl\">Mutation Score</div><div class=\"val {htmlCovClass scoreRatio}\">{htmlScore r.score}%</div><div>{r.proved + r.killed + r.timeout}/{r.tested}</div></div>"
  parts := parts.push s!"<div class=\"card\"><div class=\"lbl\">Survived</div><div class=\"val {if r.survived == 0 then "ok" else "bad"}\">{r.survived}</div><div>of {r.tested} tested</div></div>"
  parts := parts.push s!"<div class=\"card\"><div class=\"lbl\">Killed / Proved</div><div class=\"val ok\">{r.killed + r.proved}</div><div>killed {r.killed}, proved {r.proved}</div></div>"
  parts := parts.push s!"<div class=\"card\"><div class=\"lbl\">Timeout / Skipped</div><div class=\"val\">{r.timeout}</div><div>uncomp {r.uncompilable}, uncov {r.uncovered}</div></div>"
  parts := parts.push "</div>"
  parts := parts.push "<div class=\"controls\"><input id=\"mut-q\" class=\"search\" style=\"margin:0\" type=\"search\" placeholder=\"Filter file, decl, mutation...\"><select id=\"mut-out\"><option value=\"all\">All outcomes</option><option value=\"survived\">Survived</option><option value=\"killed\">Killed</option><option value=\"proved\">Proved</option><option value=\"timeout\">Timeout</option><option value=\"uncompilable\">Uncompilable</option><option value=\"uncovered\">Uncovered</option></select></div>"
  parts := parts.push "<table id=\"mut-tbl\"><thead><tr><th>Location</th><th>Declaration</th><th>Kind</th><th>Mutation</th><th>Outcome</th><th class=\"num\">Time</th></tr></thead><tbody>"
  for res in r.results do
    let m := res.mutant
    let oStr := res.outcome.toString
    let oCls := match res.outcome with
      | .killed | .proved | .timeout => "ok"
      | .survived => "bad"
      | .uncompilable | .uncovered => "warn"
    parts := parts.push s!"<tr data-o=\"{oStr}\"><td><code>{htmlEscape m.file}:{m.line}:{m.col}</code></td><td><code>{htmlEscape m.decl}</code></td><td><code>{htmlEscape m.kind.toString}</code></td><td><code>{htmlEscape m.original}</code> &rarr; <code>{htmlEscape m.replacement}</code></td><td class=\"{oCls}\">{oStr}</td><td class=\"num\">{res.elapsedMs}ms</td></tr>"
  parts := parts.push "</tbody></table>"
  parts := parts.push mutateFilterJs
  IO.FS.writeFile outFile (renderHtmlDoc "LeanCov Mutation Report" ("\n".intercalate parts.toList))

end LeanCov.Cov
