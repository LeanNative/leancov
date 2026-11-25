import LeanCov.Runtime

/-! # Deterministic coverage-guided mutation fuzzer (`LeanCov.Fuzz`)

Seed-driven byte mutator with:
- in-process AFL-bucket coverage feedback (`LeanCov.fuzzReset` / `fuzzCheckNew`) promoting
  interesting mutants into a bounded dynamic corpus (disable with `--no-guided`);
- automatic delta-debugging crash minimization before reporting/saving findings (`--no-minimize`);
- child supervision under `LEAN_ABORT_ON_PANIC=1` (turning out-of-bounds panics into caught crashes);
- a stall watchdog that kills hung parser calls and prints the exact replay command;
- optional regression corpus replay (`<corpus>/<target>/*.bin`);
- seed sanity verification (refuses to run a target whose seeds all fail to parse). -/

namespace LeanCov.Fuzz

abbrev Rng := IO.Ref UInt64

/-- SplitMix64 deterministic PRNG step. -/
def next (rng : Rng) : IO UInt64 := do
  let state := (← rng.get) + 0x9E3779B97F4A7C15
  rng.set state
  let a := (state ^^^ (state >>> 30)) * 0xBF58476D1CE4E5B9
  let b := (a ^^^ (a >>> 27)) * 0x94D049BB133111EB
  return b ^^^ (b >>> 31)

def index (rng : Rng) (upperBound : Nat) : IO Nat := do
  if upperBound == 0 then return 0
  return (← next rng).toNat % upperBound

/-- Assert an invariant inside a fuzz target; throws on violation. -/
def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

structure Target where
  name : String
  seeds : Array ByteArray
  /-- Returns `true` if the parser accepted the input; throws on any broken invariant. -/
  check : Rng → ByteArray → IO Bool
  /-- Optional grammar tokens spliced in by the mutator (useful for text/structured formats). -/
  tokens : Array ByteArray := #[]

private def bombs : Array ByteArray :=
  #[⟨#[0xFF]⟩, ⟨#[0xFD, 0xFF, 0xFF]⟩, ⟨#[0xFE, 0xFF, 0xFF, 0xFF, 0xFF]⟩,
    ⟨#[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]⟩]

private def insertAt (b piece : ByteArray) (at_ : Nat) : ByteArray :=
  b.extract 0 at_ ++ piece ++ b.extract at_ b.size

/-- Mutate `source` using bit flips, byte overwrites/insertions/deletions, truncation, block copies,
length bombs, and optional grammar tokens. -/
def mutate (source : ByteArray) (rng : Rng) (maximum : Nat) (tokens : Array ByteArray := #[]) : IO ByteArray := do
  let mut b := source.extract 0 maximum
  let one := (← index rng 2) == 0
  let many := 1 + (← index rng 8)
  let edits := if one then 1 else many
  for _ in [:edits] do
    match ← index rng (if tokens.isEmpty then 7 else 10) with
    | 0 =>
      if b.isEmpty then continue
      let i ← index rng b.size
      b := b.set! i (b[i]! ^^^ (1 <<< (← index rng 8)).toUInt8)
    | 1 =>
      if b.isEmpty then continue
      b := b.set! (← index rng b.size) (← next rng).toUInt8
    | 2 =>
      if b.size >= maximum then continue
      b := insertAt b ⟨#[(← next rng).toUInt8]⟩ (← index rng (b.size + 1))
    | 3 =>
      if b.isEmpty then continue
      let i ← index rng b.size
      b := b.extract 0 i ++ b.extract (i + 1) b.size
    | 4 =>
      if b.isEmpty then continue
      b := b.extract 0 (← index rng b.size)
    | 5 =>
      if b.isEmpty || b.size >= maximum then continue
      let start ← index rng b.size
      let length := min (1 + (← index rng (min 32 (b.size - start)))) (maximum - b.size)
      b := insertAt b (b.extract start (start + length)) (← index rng (b.size + 1))
    | 7 | 8 | 9 =>
      let token := tokens[← index rng tokens.size]!
      let room := maximum - b.size
      if room < token.size then continue
      b := insertAt b token (← index rng (b.size + 1))
    | _ =>
      let room := maximum - b.size
      if room == 0 then continue
      let bomb := bombs[← index rng bombs.size]!
      b := insertAt b (bomb.extract 0 room) (← index rng (b.size + 1))
  return b

structure Options where
  iterations : Nat := 1000
  seed : UInt64 := 0x4C45414E434F5601
  target : Option String := none
  maxInput : Nat := 16384
  save : Option System.FilePath := none
  guided : Bool := true
  minimize : Bool := true
  deriving Inhabited

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def parseNumber? (text : String) : Option Nat :=
  if text.startsWith "0x" then
    (text.drop 2).toString.foldl (fun acc c => do return (← acc) * 16 + (← hexDigit? c)) (some 0)
  else text.toNat?

private def parseOptions : List String → Options → Except String Options
  | [], o => pure o
  | "--iterations" :: v :: rest, o =>
    match parseNumber? v with
    | some n => parseOptions rest { o with iterations := n }
    | none => throw s!"--iterations {v}"
  | "--seed" :: v :: rest, o =>
    match parseNumber? v with
    | some n => parseOptions rest { o with seed := n.toUInt64 }
    | none => throw s!"--seed {v}"
  | "--target" :: v :: rest, o => parseOptions rest { o with target := if v == "all" then none else some v }
  | "--max-input" :: v :: rest, o =>
    match parseNumber? v with
    | some n => parseOptions rest { o with maxInput := n }
    | none => throw s!"--max-input {v}"
  | "--save" :: v :: rest, o => parseOptions rest { o with save := some v }
  | "--no-guided" :: rest, o => parseOptions rest { o with guided := false }
  | "--no-minimize" :: rest, o => parseOptions rest { o with minimize := false }
  | other :: _, _ => throw s!"unknown argument {other}"

private def seedHex (seed : UInt64) : String := "0x" ++ String.ofList (Nat.toDigits 16 seed.toNat)

private def hex (b : ByteArray) : String :=
  b.foldl (fun acc x => acc ++ (String.ofList (Nat.toDigits 16 (x.toNat / 16 % 16) ++ Nat.toDigits 16 (x.toNat % 16)))) ""

private def say (line : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn line
  out.flush

private def replayLine (exe : String) (o : Options) (targets : String) (iteration : Nat) : String :=
  s!"{exe} --target {targets} --seed {seedHex o.seed} --max-input {o.maxInput} --iterations {iteration + 1}"

private def failsWith (t : Target) (cand : ByteArray) : IO Bool := do
  let rng ← IO.mkRef 1
  try
    let _ ← t.check rng cand
    return false
  catch _ =>
    return true

/-- Delta-debugging shrinker: iteratively deletes chunks while `t.check` still throws. -/
def minimizeInput (t : Target) (input : ByteArray) (budget : Nat := 128) : IO ByteArray := do
  let mut best := input
  let mut remaining := budget
  let mut stride := max 1 (best.size / 2)
  while stride > 0 && best.size > 1 && remaining > 0 do
    let mut progressed := false
    let mut i := 0
    while i < best.size && best.size > 1 && remaining > 0 do
      let delEnd := min best.size (i + stride)
      let cand := best.extract 0 i ++ best.extract delEnd best.size
      remaining := remaining - 1
      if ← failsWith t cand then
        best := cand
        progressed := true
      else
        i := i + stride
    if !progressed then
      stride := stride / 2
  return best

private def attempt (t : Target) (rng : Rng) (input : ByteArray) (o : Options) (where_ : String)
    (allowMinimize : Bool := false) : IO Bool := do
  try t.check rng input
  catch e =>
    let finalInput ←
      if allowMinimize && o.minimize && input.size > 1 then minimizeInput t input
      else pure input
    let minNote :=
      if finalInput.size < input.size then s!" (minimized {input.size}B -> {finalInput.size}B)"
      else ""
    IO.eprintln s!"fuzz: FINDING target={t.name} {where_}{minNote}: {e}"
    if finalInput.size ≤ 4096 then IO.eprintln s!"fuzz: input {hex finalInput}"
    if let some dir := o.save then
      IO.FS.createDirAll dir
      IO.FS.writeBinFile (dir / s!"{t.name}-{seedHex o.seed}.bin") finalInput
    IO.Process.exit 1

private def replayCorpus (targets : Array Target) (corpus : System.FilePath) (o : Options) : IO Nat := do
  unless ← corpus.isDir do throw (IO.userError s!"no corpus at {corpus}")
  let rng ← IO.mkRef 0x4C45_414E_434F_5602
  let mut replayed := 0
  for entry in (← corpus.readDir) do
    let some t := targets.find? (·.name == entry.fileName)
      | throw (IO.userError s!"{entry.path} names no fuzz target")
    for file in (← entry.path.readDir) do
      if file.path.extension != some "bin" then continue
      discard <| attempt t rng (← IO.FS.readBinFile file.path) o s!"corpus {file.path}"
      replayed := replayed + 1
  return replayed

private structure Tally where
  took : Nat := 0
  slowestMs : Nat := 0
  corpusAdds : Nat := 0
  deriving Inhabited

private def maxDynamicCorpus : Nat := 512

private def pickCorpusInput (corp : Array ByteArray) (seedCount : Nat) (rng : Rng) : IO ByteArray := do
  if corp.size > seedCount && (← index rng 4) != 0 then
    let recentStart := if corp.size - seedCount > 16 then corp.size - 16 else seedCount
    let idx := recentStart + (← index rng (corp.size - recentStart))
    return corp[idx]!
  return corp[← index rng corp.size]!

private def child (all : Array Target) (o : Options) (exe : String) (corpus : Option System.FilePath)
    (marker : System.FilePath) : IO UInt32 := do
  let targets : Array Target := match o.target with
    | some n => all.filter fun (t : Target) => t.name == n
    | none => all
  if targets.isEmpty then
    IO.eprintln s!"fuzz: no target {o.target.getD ""}: {all.map Target.name}"
    return 2
  let selection := o.target.getD "all"
  let replayed ← match corpus with
    | some dir => do
      IO.FS.writeFile marker "the corpus\n"
      replayCorpus all dir o
    | none => pure 0
  let seedRng ← IO.mkRef 1
  for t in targets do
    IO.FS.writeFile marker s!"target={t.name}'s seeds\n"
    let mut anyTaken := false
    for s in t.seeds do
      anyTaken := (← attempt t seedRng s o "a seed") || anyTaken
    unless anyTaken do
      IO.eprintln s!"fuzz: target={t.name}: no seed parses, so its fuzzing would only test refusals"
      return 1
  say s!"fuzz: seed={seedHex o.seed} iterations={o.iterations} max-input={o.maxInput} targets={selection} guided={o.guided}"
  if o.guided then LeanCov.fuzzReset ()
  let rng ← IO.mkRef o.seed
  let mut tallies : Array Tally := targets.map fun _ => {}
  let mut corpora : Array (Array ByteArray) := targets.map (·.seeds)
  for iteration in [:o.iterations] do
    for h : k in [:targets.size] do
      let t := targets[k]'h.2.1
      IO.FS.writeFile marker s!"target={t.name} iteration={iteration}\n{replayLine exe o selection iteration}\n"
      let corp := corpora[k]!
      let base ← pickCorpusInput corp t.seeds.size rng
      let input ← mutate base rng o.maxInput t.tokens
      if let some dir := o.save then
        IO.FS.createDirAll dir
        IO.FS.writeBinFile (dir / "in-flight.bin") input
      let start ← IO.monoMsNow
      let took ← attempt t rng input o
        s!"seed={seedHex o.seed} iteration={iteration}: replay: {replayLine exe o selection iteration}"
        (allowMinimize := true)
      let ms := (← IO.monoMsNow) - start
      let mut added : Nat := 0
      if o.guided then
        let newEdges ← LeanCov.fuzzCheckNew ()
        if newEdges.toNat > 0 && corp.size < maxDynamicCorpus then
          corpora := corpora.set! k (corp.push input)
          added := 1
      tallies := tallies.modify k fun c =>
        { took := c.took + (if took then 1 else 0)
          slowestMs := max c.slowestMs ms
          corpusAdds := c.corpusAdds + added }
  for h : k in [:targets.size] do
    let t := targets[k]'h.2.1
    let c := tallies[k]!
    let corpNote := if c.corpusAdds > 0 then s!", corpus +{c.corpusAdds}" else ""
    say s!"  {t.name}: took {c.took} of {o.iterations}{corpNote}, slowest {c.slowestMs} ms"
  let covNote ←
    if o.guided then
      let cov ← LeanCov.fuzzCoveredSites ()
      if cov.toNat > 0 then pure s!", {cov} sites covered" else pure ""
    else pure ""
  say s!"fuzz: passed {o.iterations * targets.size} cases and {replayed} corpus inputs (seed {seedHex o.seed}{covNote})"
  return 0

/-- Seconds without progress before the parent supervisor kills the child as a hang finding. -/
def stallSeconds : Nat := 30

private def parent (args : List String) (exe : String) (marker : System.FilePath) : IO UInt32 := do
  let spawned ← IO.Process.spawn {
    cmd := exe, args := args.toArray
    env := #[("LEAN_ABORT_ON_PANIC", some "1"), ("LEANCOV_FUZZ_MARKER", some marker.toString)] }
  let readMarker : IO String := do
    try IO.FS.readFile marker catch _ => pure ""
  let rec watch (last : String) (still : Nat) (fuel : Nat) : IO UInt32 := do
    match fuel with
    | 0 => return 3
    | fuel + 1 =>
      IO.sleep 1000
      if let some code ← spawned.tryWait then return code
      let now ← readMarker
      if now.isEmpty || now != last then return ← watch now 0 fuel
      if still + 1 < stallSeconds then return ← watch now (still + 1) fuel
      spawned.kill
      IO.eprintln s!"fuzz: FINDING: no progress for {stallSeconds} s in\n{now}"
      return 1
  let code ← watch "" 0 (100 * 24 * 3600)
  if code != 0 && code != 1 && code != 2 then
    IO.eprintln s!"fuzz: FINDING: the run crashed (exit {code}) in\n{← readMarker}"
    return 1
  return code

/-- Entry point for a fuzz executable. Pass `corpus := none` if no regression corpus directory is used. -/
def main (targets : Array Target) (args : List String) (corpus : Option System.FilePath := none) : IO UInt32 := do
  let options ← match parseOptions args {} with
    | .ok o => pure o
    | .error e =>
      IO.eprintln s!"fuzz: {e}\nusage: fuzz [--iterations N] [--seed N|0xHEX] [--target NAME|all] [--max-input N] [--save DIR] [--no-guided] [--no-minimize]"
      return 2
  let exe := (← IO.appPath).toString
  match ← IO.getEnv "LEANCOV_FUZZ_MARKER" with
  | some marker => child targets options exe corpus marker
  | none =>
    let (_, marker) ← IO.FS.createTempFile
    let code ← parent args exe marker
    try IO.FS.removeFile marker catch _ => pure ()
    IO.Process.exit code.toUInt8

end LeanCov.Fuzz