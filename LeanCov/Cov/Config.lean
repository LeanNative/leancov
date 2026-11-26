import LeanCov.Cov.Types
import LeanCov.Cov.Report

/-! # Declarative Project Configuration (`leancov.toml`) Parser -/

namespace LeanCov.Cov

/-- Configuration for one Lake package staged and instrumented by `leancov test`. -/
structure PackageConfig where
  name : String := ""
  pkg : String := "."
  srcDirs : Array String := #[]
  pathPrefix : String := ""
  exclude : Array String := #[]
  imports : Array String := #[]
  deps : Array String := #[]
  boolOps : Bool := true
  includeCafs : Bool := false
  isSelf : Bool := false
  deriving Repr, BEq, Inhabited

/-- Configuration for one executable test suite run by `leancov test`. -/
structure SuiteConfig where
  name : String := ""
  package : String := ""
  target : String := ""
  args : Array String := #[]
  cwd : Option String := none
  fast : Bool := true
  deriving Repr, BEq, Inhabited

/-- Top-level `leancov.toml` configuration for multi-package test & report orchestration. -/
structure ProjectConfig where
  out : String := "build/leancov"
  jobs : Nat := 4
  sort : SortKey := .cog
  top : Nat := 20
  files : Bool := true
  kinds : Bool := true
  html : Bool := false
  markdown : Bool := false
  excludeInstances : Bool := false
  excludeKinds : Array BranchKind := #[]
  minCov : Option Float := none
  maxCrap : Option Float := none
  maxCogCrap : Option Float := none
  packages : Array PackageConfig := #[]
  suites : Array SuiteConfig := #[]
  deriving Repr, BEq, Inhabited

/-- Parse a non-negative decimal float or integer string. -/
def parseFloatStr? (s : String) : Option Float :=
  let t := s.trimAscii.copy
  match t.splitOn "." with
  | [whole] => whole.toNat?.map Float.ofNat
  | [whole, frac] =>
    match whole.toNat?, frac.toNat? with
    | some w, some f =>
      let denom := Float.pow 10.0 (Float.ofNat frac.length)
      some (Float.ofNat w + Float.ofNat f / denom)
    | _, _ => none
  | _ => none

private def stripTomlComment (line : String) : String := Id.run do
  let mut out := ""
  let mut inStr := false
  let mut esc := false
  for c in line.toList do
    if esc then
      out := out.push c; esc := false
    else if inStr && c == '\\' then
      out := out.push c; esc := true
    else if c == '"' then
      inStr := !inStr; out := out.push c
    else if !inStr && c == '#' then
      break
    else
      out := out.push c
  return out.trimAscii.copy

private def bracketDelta (line : String) : Int := Id.run do
  let mut d : Int := 0
  let mut inStr := false
  let mut esc := false
  for c in line.toList do
    if esc then esc := false
    else if inStr && c == '\\' then esc := true
    else if c == '"' then inStr := !inStr
    else if !inStr && c == '[' then d := d + 1
    else if !inStr && c == ']' then d := d - 1
  return d

private def normalizeTomlLines (toml : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut buf := ""
  let mut depth : Int := 0
  for raw in toml.splitOn "\n" do
    let clean := stripTomlComment raw
    if clean.isEmpty then continue
    buf := if buf.isEmpty then clean else buf ++ " " ++ clean
    depth := depth + bracketDelta clean
    if depth ≤ 0 then
      out := out.push buf
      buf := ""
      depth := 0
  if !buf.isEmpty then out := out.push buf
  return out

private def parseTomlStr (raw : String) : Except String String :=
  let t := raw.trimAscii.copy
  if t.length ≥ 2 && t.startsWith "\"" && t.endsWith "\"" then
    .ok ((t.drop 1).dropEnd 1).toString
  else
    .error s!"expected quoted string, got: {t}"

private def parseTomlBool (raw : String) : Except String Bool :=
  match raw.trimAscii.copy with
  | "true" => .ok true
  | "false" => .ok false
  | t => .error s!"expected true|false, got: {t}"

private def parseTomlNat (raw : String) : Except String Nat :=
  match raw.trimAscii.copy.toNat? with
  | some n => .ok n
  | none => .error s!"expected integer, got: {raw}"

private def parseTomlStrArray (raw : String) : Except String (Array String) := do
  let t := raw.trimAscii.copy
  unless t.startsWith "[" && t.endsWith "]" do
    throw s!"expected string array `[...]`, got: {t}"
  let inner := ((t.drop 1).dropEnd 1).toString.trimAscii.copy
  if inner.isEmpty then return #[]
  let mut items : Array String := #[]
  let mut i : List Char := inner.toList
  let mut cur := ""
  let mut inStr := false
  let mut esc := false
  let mut expectComma := false
  while !i.isEmpty do
    let c := i.head!
    i := i.tail!
    if inStr then
      if esc then cur := cur.push c; esc := false
      else if c == '\\' then esc := true
      else if c == '"' then items := items.push cur; cur := ""; inStr := false; expectComma := true
      else cur := cur.push c
    else if c == ' ' || c == '\t' || c == '\r' || c == '\n' then
      continue
    else if expectComma then
      if c == ',' then expectComma := false
      else throw s!"expected ',' in array near `{c}`"
    else if c == '"' then
      inStr := true
    else
      throw s!"expected quoted string in array near `{c}`"
  if inStr then throw "unterminated string in array"
  return items

private inductive ConfigSection where
  | root
  | pkg (p : PackageConfig)
  | suite (s : SuiteConfig)

private def setRootField (cfg : ProjectConfig) (k v : String) : Except String ProjectConfig := do
  match k with
  | "out" => return { cfg with out := ← parseTomlStr v }
  | "jobs" => return { cfg with jobs := ← parseTomlNat v }
  | "sort" =>
    let sv ← parseTomlStr v
    let some sk := SortKey.ofString? sv | throw s!"invalid sort key '{sv}'"
    return { cfg with sort := sk }
  | "top" => return { cfg with top := ← parseTomlNat v }
  | "files" => return { cfg with files := ← parseTomlBool v }
  | "kinds" => return { cfg with kinds := ← parseTomlBool v }
  | "html" => return { cfg with html := ← parseTomlBool v }
  | "markdown" => return { cfg with markdown := ← parseTomlBool v }
  | "exclude_instances" => return { cfg with excludeInstances := ← parseTomlBool v }
  | "exclude_kinds" =>
    let ks ← (← parseTomlStrArray v).mapM fun s =>
      match BranchKind.ofString? s with
      | some bk => .ok bk
      | none => .error s!"invalid branch kind '{s}'"
    return { cfg with excludeKinds := ks }
  | "min_cov" =>
    let some f := parseFloatStr? v | throw s!"invalid float '{v}'"
    return { cfg with minCov := some f }
  | "max_crap" =>
    let some f := parseFloatStr? v | throw s!"invalid float '{v}'"
    return { cfg with maxCrap := some f }
  | "max_cog_crap" =>
    let some f := parseFloatStr? v | throw s!"invalid float '{v}'"
    return { cfg with maxCogCrap := some f }
  | _ => throw s!"unknown [leancov] option '{k}'"

private def setPkgField (p : PackageConfig) (k v : String) : Except String PackageConfig := do
  match k with
  | "name" => return { p with name := ← parseTomlStr v }
  | "pkg" => return { p with pkg := ← parseTomlStr v }
  | "src_dirs" => return { p with srcDirs := ← parseTomlStrArray v }
  | "prefix" => return { p with pathPrefix := ← parseTomlStr v }
  | "exclude" => return { p with exclude := ← parseTomlStrArray v }
  | "imports" => return { p with imports := ← parseTomlStrArray v }
  | "deps" => return { p with deps := ← parseTomlStrArray v }
  | "bool_ops" => return { p with boolOps := ← parseTomlBool v }
  | "include_cafs" => return { p with includeCafs := ← parseTomlBool v }
  | "self" => return { p with isSelf := ← parseTomlBool v }
  | _ => throw s!"unknown [[package]] option '{k}'"

private def setSuiteField (s : SuiteConfig) (k v : String) : Except String SuiteConfig := do
  match k with
  | "name" => return { s with name := ← parseTomlStr v }
  | "package" => return { s with package := ← parseTomlStr v }
  | "target" => return { s with target := ← parseTomlStr v }
  | "args" => return { s with args := ← parseTomlStrArray v }
  | "cwd" => return { s with cwd := some (← parseTomlStr v) }
  | "fast" => return { s with fast := ← parseTomlBool v }
  | _ => throw s!"unknown [[suite]] option '{k}'"

private def flushSection (cfg : ProjectConfig) : ConfigSection → Except String ProjectConfig
  | .root => .ok cfg
  | .pkg p =>
    if p.name.isEmpty then .error "[[package]] entry requires `name`"
    else .ok { cfg with packages := cfg.packages.push p }
  | .suite s =>
    if s.name.isEmpty || s.package.isEmpty then .error "[[suite]] entry requires `name` and `package`"
    else
      let tgt := if s.target.isEmpty then s.name else s.target
      .ok { cfg with suites := cfg.suites.push { s with target := tgt } }

/-- Parse a `leancov.toml` manifest for multi-package staging, execution, and reporting. -/
def parseProjectConfig (toml : String) : Except String ProjectConfig := do
  let mut cfg : ProjectConfig := {}
  let mut sec : ConfigSection := .root
  for line in normalizeTomlLines toml do
    if line == "[leancov]" then
      cfg ← flushSection cfg sec
      sec := .root
    else if line == "[[package]]" then
      cfg ← flushSection cfg sec
      sec := .pkg {}
    else if line == "[[suite]]" then
      cfg ← flushSection cfg sec
      sec := .suite {}
    else if line.startsWith "[" then
      throw s!"unknown section header '{line}'"
    else
      match line.splitOn "=" with
      | kRaw :: valParts =>
        if valParts.isEmpty then throw s!"expected `key = value`, got: {line}"
        let k := kRaw.trimAscii.copy
        let v := ("=".intercalate valParts).trimAscii.copy
        match sec with
        | .root => cfg ← setRootField cfg k v
        | .pkg p => sec := .pkg (← setPkgField p k v)
        | .suite s => sec := .suite (← setSuiteField s k v)
      | [] => throw s!"invalid line: {line}"
  cfg ← flushSection cfg sec
  if cfg.packages.isEmpty then throw "leancov.toml requires at least one [[package]] entry"
  for s in cfg.suites do
    if !cfg.packages.any (·.name == s.package) then
      throw s!"suite '{s.name}' references unknown package '{s.package}'"
  return cfg

end LeanCov.Cov
