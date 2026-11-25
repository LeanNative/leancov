import Lean.Data.Json

/-! # Core data model and binary `.cov` profile I/O for LeanCov -/

namespace LeanCov.Cov
open Lean

/-- Source-level branch kind recorded at each instrumentation probe. -/
inductive BranchKind where
  | ifThen
  | ifElse
  | unlessEnter
  | unlessSkip
  | matchArm
  | letElseOk
  | letElseFail
  | loopBody
  | loopSkip
  | catchBody
  | andTrue
  | andFalse
  | orTrue
  | orFalse
  | fnEntry
  deriving Repr, BEq, Inhabited

/-- True for genuine control-flow / decision branch outcomes (excludes straight-line `fn.entry`). -/
def BranchKind.isBranch : BranchKind → Bool
  | .fnEntry => false
  | _ => true

def BranchKind.toString : BranchKind → String
  | .ifThen => "if.then"
  | .ifElse => "if.else"
  | .unlessEnter => "unless.enter"
  | .unlessSkip => "unless.skip"
  | .matchArm => "match.arm"
  | .letElseOk => "letElse.ok"
  | .letElseFail => "letElse.fail"
  | .loopBody => "loop.body"
  | .loopSkip => "loop.skip"
  | .catchBody => "catch.body"
  | .andTrue => "and.true"
  | .andFalse => "and.false"
  | .orTrue => "or.true"
  | .orFalse => "or.false"
  | .fnEntry => "fn.entry"

def BranchKind.ofString? : String → Option BranchKind
  | "if.then" => some .ifThen
  | "if.else" => some .ifElse
  | "unless.enter" => some .unlessEnter
  | "unless.skip" => some .unlessSkip
  | "match.arm" => some .matchArm
  | "letElse.ok" => some .letElseOk
  | "letElse.fail" => some .letElseFail
  | "loop.body" => some .loopBody
  | "loop.skip" => some .loopSkip
  | "catch.body" => some .catchBody
  | "and.true" => some .andTrue
  | "and.false" => some .andFalse
  | "or.true" => some .orTrue
  | "or.false" => some .orFalse
  | "fn.entry" => some .fnEntry
  | _ => none

instance : ToJson BranchKind := ⟨fun k => Json.str k.toString⟩
instance : FromJson BranchKind where
  fromJson? j := do
    let s ← j.getStr?
    match BranchKind.ofString? s with
    | some k => pure k
    | none => throw s!"unknown branch kind: {s}"

/-- One instrumented probe site in a Lean source file. -/
structure Site where
  id : Nat
  file : String
  decl : String
  line : Nat
  col : Nat
  kind : BranchKind
  nesting : Nat := 0
  deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- Static complexity and probe-site summary for one Lean declaration. -/
structure FuncInfo where
  name : String
  file : String
  line : Nat
  endLine : Nat
  lines : Nat
  cc : Nat
  cognitive : Nat
  siteIds : Array Nat := #[]
  deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- Instrumentation manifest (`sites.json`) linking binary counter indices to Lean source locations. -/
structure Manifest where
  version : Nat := 1
  armOnMain : Bool := false
  sites : Array Site := #[]
  functions : Array FuncInfo := #[]
  skippedFiles : Array (String × String) := #[]
  deriving Repr, Inhabited, ToJson, FromJson

/-! ## Binary `.cov` profile format (`LCOV0001` + `u64 count` + `u64[count]`) -/

def profileMagic : ByteArray := "LCOV0001".toUTF8
def profileHeaderBytes : Nat := 16

private def pushU64LE (b : ByteArray) (v : UInt64) : ByteArray := Id.run do
  let mut out := b
  for i in [:8] do
    out := out.push ((v >>> (i * 8).toUInt64) &&& 0xFF).toUInt8
  return out

private def readU64LE (b : ByteArray) (off : Nat) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  for i in [:8] do
    let byte := b.get! (off + i)
    v := v ||| (byte.toUInt64 <<< (i * 8).toUInt64)
  return v

/-- Pre-create a zeroed `.cov` file for `siteCount` sites before launching an instrumented process. -/
def initProfile (path : System.FilePath) (siteCount : Nat) : IO Unit := do
  if let some p := path.parent then IO.FS.createDirAll p
  let mut buf := ByteArray.emptyWithCapacity (profileHeaderBytes + siteCount * 8)
  buf := buf ++ profileMagic
  buf := pushU64LE buf siteCount.toUInt64
  for _ in [:siteCount * 8] do
    buf := buf.push 0
  IO.FS.writeBinFile path buf

/-- Write a hit counter array to a binary `.cov` profile file. -/
def writeProfile (path : System.FilePath) (hits : Array UInt64) : IO Unit := do
  if let some p := path.parent then IO.FS.createDirAll p
  let mut buf := ByteArray.emptyWithCapacity (profileHeaderBytes + hits.size * 8)
  buf := buf ++ profileMagic
  buf := pushU64LE buf hits.size.toUInt64
  for h in hits do
    buf := pushU64LE buf h
  IO.FS.writeBinFile path buf

/-- Read a `.cov` counter file into an array of hit counts. -/
def readProfile (path : System.FilePath) : IO (Array UInt64) := do
  let data ← IO.FS.readBinFile path
  if data.size < profileHeaderBytes then
    throw (IO.userError s!"{path}: profile too short ({data.size} bytes)")
  if data.extract 0 8 != profileMagic then
    throw (IO.userError s!"{path}: bad profile magic")
  let count := (readU64LE data 8).toNat
  let expected := profileHeaderBytes + count * 8
  if data.size < expected then
    throw (IO.userError s!"{path}: truncated profile ({data.size} < {expected} bytes)")
  let mut hits := Array.mkEmpty count
  for i in [:count] do
    hits := hits.push (readU64LE data (profileHeaderBytes + i * 8))
  return hits

/-- Merge multiple `.cov` profiles by summing hit counts per site (saturating on overflow). -/
def mergeProfiles (paths : Array System.FilePath) (siteCount : Nat) : IO (Array UInt64) := do
  let mut total := Array.replicate siteCount (0 : UInt64)
  for p in paths do
    let hits ← readProfile p
    let n := min total.size hits.size
    for i in [:n] do
      let a := total[i]!
      let b := hits[i]!
      let sum := if a > UInt64.size.toUInt64 - 1 - b then UInt64.size.toUInt64 - 1 else a + b
      total := total.set! i sum
  return total

/-- CRAP formula: `C^2 * (1 - cov)^3 + C`. -/
def crapScore (complexity : Nat) (cov : Float) : Float :=
  let c := Float.ofNat complexity
  let u := 1.0 - cov
  c * c * u * u * u + c

end LeanCov.Cov
