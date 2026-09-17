import Fern
import FernImpl

/-!
# `fern-solve`: the exact fewest-same-finger-bigram search

```
fern-solve count [--skipgrams | --spacegrams] TEXT   print the 900-entry count table as TSV
fern-solve check TEXT TABLE                           compare a TSV table with the text's counts
fern-solve solve TABLE                                find the optimum and a layout achieving it
fern-solve cert NAME TABLE RESULT                     emit a kernel-checked certificate for a result
fern-solve tiecert NAME SPACEGRAMS RESULT             emit the kernel-checked spacegram tie-break
```

What is proved and what is trusted:

- `count` and `check` read the text through `Fern.Solver.countLines`, which is proved to equal
  `bigramCount (textKeymap.bigramsOf (joinLines lines))`. File reading and line splitting are
  trusted, and so is the TSV parser; `check` compares all 900 entries of a table against the text.
- `solve` computes `FernImpl.solveValue (swTable cnt) (fill (swTable cnt))`, which is by definition
  the value inside `FernImpl.solve cnt`, and `Fern.Solver.solve_isLeast` proves that value is the
  least same-finger weight over every layout. Finding a layout that achieves it is unverified: the
  pieces are rebuilt from the table, and their cost is recomputed directly from the count table and
  must equal the proved optimum.
-/

open Fern.Solver FernImpl

/-! ### Count tables as TSV -/

def keyChar (i : Nat) : Char := keyChars.getD i '?'

def keyIndex (c : Char) : Option Nat := keyChars.idxOf? c

def renderTable (header : List String) (tbl : Array Nat) : String := Id.run do
  let mut out := ""
  for h in header do
    out := out ++ "# " ++ h ++ "\n"
  for a in [0:30] do
    for b in [0:30] do
      out := out ++ s!"{keyChar a}\t{keyChar b}\t{tbl.getD (a * 30 + b) 0}\n"
  return out

/-- Parse a TSV count table. Every one of the 900 key pairs must appear exactly once. -/
def parseTable (src : String) : Except String (Array Nat) := do
  let mut tbl := Array.replicate 900 0
  let mut seen := Array.replicate 900 false
  let mut lineNo := 0
  for line in src.splitOn "\n" do
    lineNo := lineNo + 1
    let line := line.trimAsciiEnd.toString
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn "\t" with
    | [sa, sb, sn] =>
      let some a := (match sa.toList with | [c] => keyIndex c | _ => none)
        | throw s!"line {lineNo}: unknown key {sa.quote}"
      let some b := (match sb.toList with | [c] => keyIndex c | _ => none)
        | throw s!"line {lineNo}: unknown key {sb.quote}"
      let some n := sn.toNat? | throw s!"line {lineNo}: bad count {sn.quote}"
      let i := a * 30 + b
      if seen[i]! then throw s!"line {lineNo}: pair {sa}{sb} repeated"
      tbl := tbl.set! i n
      seen := seen.set! i true
    | _ => throw s!"line {lineNo}: expected three tab-separated fields"
  for i in [0:900] do
    if !seen[i]! then throw s!"pair {keyChar (i / 30)}{keyChar (i % 30)} missing"
  return tbl

def readTable (path : System.FilePath) : IO (Array Nat) := do
  match parseTable (← IO.FS.readFile path) with
  | .ok tbl => return tbl
  | .error e => throw (IO.userError s!"{path}: {e}")

/-! ### Reading text -/

def readLines (path : System.FilePath) : IO (List (List Char)) := do
  return (← IO.FS.lines path).toList.map String.toList

/-- Skipgram or spacegram counts, one line at a time. Neither kind crosses a newline, since a
newline is neither mapped nor a space. -/
def countGramsLines (grams : List Char → List (Fern.Ortholinear.Bigram (Fin 30)))
    (ls : List (List Char)) : Array Nat :=
  ls.foldl (fun acc l => countInto acc (grams l)) (Array.replicate 900 0)

def totalOf (tbl : Array Nat) : Nat := tbl.foldl (· + ·) 0

/-! ### Finding a layout that achieves the optimum (unverified) -/

/-- Like `scanStep`, but keeps the mask: the value in the high bits, the mask in the low 30. -/
@[inline] def argStep (sw t : @& ByteArray) (m best : UInt64) : UInt64 :=
  if pop30 m == 12 then
    let packed := ((indexCost sw m + step sw t (FULL ^^^ m)) <<< 30) ||| m
    if packed < best then packed else best
  else best

/-- Larger than any packed value. -/
def NOMASK : UInt64 := 0xFFFFFFFFFFFFFFFF

def argSolve (sw t : @& ByteArray) : UInt64 :=
  let tasks := (List.range 1024).map fun c =>
    Task.spawn fun _ => scanWith (argStep sw t) (2 ^ 20) (c * 2 ^ 20).toUInt64 NOMASK
  tasks.foldl (fun acc tk => let v := tk.get; if v < acc then v else acc) NOMASK

def bitsOf (m : UInt64) : List Nat :=
  (List.range 30).filter fun i => (m >>> i.toUInt64) &&& 1 == 1

def maskOf (keys : List Nat) : UInt64 :=
  keys.foldl (fun m i => m ||| bit i.toUInt64) 0

/-- Same-finger weight of a piece, straight from the count table. -/
def pieceCostOf (tbl : Array Nat) (piece : List Nat) : Nat :=
  (piece.map fun x => ((piece.filter (· != x)).map fun y => tbl.getD (x * 30 + y) 0).sum).sum

/-- All `k`-element sublists. -/
def choose : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (choose k xs).map (x :: ·) ++ choose (k + 1) xs

/-- The two index pieces: the split of the twelve keys achieving `target`. -/
def splitIndex (tbl : Array Nat) (keys : List Nat) (target : Nat) : Option (List Nat × List Nat) :=
  match keys with
  | [] => none
  | a :: rest =>
    (choose 5 rest).findSome? fun A =>
      let B := rest.filter (· ∉ A)
      if pieceCostOf tbl (a :: A) + pieceCostOf tbl B == target then some (a :: A, B) else none

/-- Triples of mask `m` achieving `target`, reading the smaller key sets from the table. -/
def splitTriples (sw t : ByteArray) : Nat → UInt64 → UInt64 → Option (List (List Nat))
  | 0, _, _ => some []
  | fuel + 1, m, target =>
    if m == 0 then some [] else
    let a := hibit m
    let r := m ^^^ bit a
    (bitsOf r).findSome? fun b =>
      (bitsOf (r &&& (bit b.toUInt64 - 1))).findSome? fun c =>
        let r2 := r ^^^ bit b.toUInt64 ^^^ bit c.toUInt64
        let cell := (get32 t r2.toNat).toUInt64
        if sw32 sw a b.toUInt64 + sw32 sw a c.toUInt64 + sw32 sw b.toUInt64 c.toUInt64 + cell == target then
          (splitTriples sw t fuel r2 cell).map ([a.toNat, b, c] :: ·)
        else none

def pieceString (piece : List Nat) : String := String.ofList (piece.map keyChar)

/-- One arrangement of the pieces on the 3×10 grid: simple columns outside, index blocks inside.
Rows, hands and column order are free; any arrangement has the same same-finger bigrams. -/
def gridOf (simple : List (List Nat)) (index : List (List Nat)) : List String :=
  let col (p : List Nat) (r : Nat) : Char := keyChar (p.getD r 0)
  let s := simple.toArray
  let x := index.toArray
  (List.range 3).map fun r =>
    let left := [col s[0]! r, col s[1]! r, col s[2]! r, col x[0]! (2 * r), col x[0]! (2 * r + 1)]
    let right := [col x[1]! (2 * r), col x[1]! (2 * r + 1), col s[3]! r, col s[4]! r, col s[5]! r]
    String.intercalate " " ((left ++ right).map toString)

/-! ### Commands -/

def timed {α : Type} (label : String) (x : Unit → α) : IO α := do
  let t0 ← IO.monoMsNow
  let v ← IO.lazyPure x
  let t1 ← IO.monoMsNow
  IO.eprintln s!"{label}: {(t1 - t0) / 1000}.{(t1 - t0) % 1000 / 100}s"
  return v

def cmdCount (kind : String) (path : System.FilePath) : IO UInt32 := do
  let ls ← readLines path
  let (tbl, what) := match kind with
    | "--skipgrams" => (countGramsLines textKeymap.skipgramsOf ls, "skipgram (key, key, key; outer pair)")
    | "--spacegrams" => (countGramsLines textKeymap.spacegramsOf ls, "spacegram (key, space, key; outer pair)")
    | _ => (countLines ls, "bigram")
  IO.print (renderTable [s!"fern {what} counts", s!"keys: {String.ofList keyChars}, case-folded",
    s!"source: {path.fileName.getD path.toString}", s!"lines: {ls.length}", s!"total: {totalOf tbl}"] tbl)
  return 0

def cmdCheck (text table : System.FilePath) : IO UInt32 := do
  let fromText := countLines (← readLines text)
  let fromTable ← readTable table
  let mut bad := 0
  for a in [0:30] do
    for b in [0:30] do
      let i := a * 30 + b
      if fromText.getD i 0 != fromTable.getD i 0 then
        bad := bad + 1
        IO.eprintln s!"{keyChar a}{keyChar b}: text {fromText.getD i 0}, table {fromTable.getD i 0}"
  IO.println s!"{900 - bad} of 900 entries agree"
  return if bad == 0 then 0 else 1

def cmdSolve (table : System.FilePath) : IO UInt32 := do
  let tbl ← readTable table
  let cnt : Nat → Nat → Nat := fun a b => if a < 30 ∧ b < 30 then tbl.getD (a * 30 + b) 0 else 0
  if totalWeight cnt ≥ 2 ^ 32 then
    IO.eprintln s!"total weight {totalWeight cnt} does not fit the 32-bit table"
    return 1
  let sw := swTable cnt
  let t ← timed "fill" fun _ => fill sw
  let value ← timed "search (proved)" fun _ => (solveValue sw t).toNat
  IO.println s!"# least same-finger weight: {value}"
  let packed ← timed "search (keeping the mask)" fun _ => argSolve sw t
  let S := packed &&& FULL
  if (packed >>> 30).toNat != value then
    IO.eprintln s!"mask search found {(packed >>> 30).toNat}, expected {value}"
    return 1
  let some (A, B) := splitIndex tbl (bitsOf S).reverse (indexCost sw S).toNat
    | IO.eprintln "could not rebuild the index split"; return 1
  let comp := FULL ^^^ S
  let some triples := splitTriples sw t 6 comp (step sw t comp)
    | IO.eprintln "could not rebuild the triples"; return 1
  let pieces := A :: B :: triples
  let cost := (pieces.map (pieceCostOf tbl)).sum
  let keys := (pieces.flatten.mergeSort (· ≤ ·))
  if cost != value || keys != List.range 30 then
    IO.eprintln s!"rebuilt pieces cost {cost}, keys {keys}"
    return 1
  IO.println s!"value {value}"
  for p in pieces do
    IO.println s!"piece {String.intercalate " " (p.map toString)}"
  IO.println "# pieces achieving it (each piece is one finger), with their weights:"
  for p in pieces do
    IO.println s!"#   {pieceString p}\t{pieceCostOf tbl p}"
  IO.println "# one layout with these pieces:"
  for row in gridOf triples [A, B] do
    IO.println s!"#   {row}"
  return 0

/-- Read the `value` and `piece` lines that `solve` prints. -/
def parseResult (src : String) : Except String (Nat × List (List Nat)) := do
  let mut value := none
  let mut pieces := #[]
  for line in src.splitOn "\n" do
    match (line.trimAsciiEnd.toString.splitOn " ").filter (· != "") with
    | ["value", n] =>
      let some v := n.toNat? | throw s!"bad value {n.quote}"
      value := some v
    | "piece" :: keys =>
      let some ks := keys.mapM String.toNat? | throw s!"bad piece {line.quote}"
      pieces := pieces.push ks
    | _ => pure ()
  let some v := value | throw "no value line"
  return (v, pieces.toList)

def lowerFirst (s : String) : String :=
  match s.toList with
  | c :: cs => String.ofList (c.toLower :: cs)
  | [] => s

/-- A Lean module certifying, by kernel evaluation alone, that the pieces cost the reported value. -/
def cmdCert (name : String) (table result : System.FilePath) : IO UInt32 := do
  let src ← IO.FS.readFile table
  let tbl ← match parseTable src with
    | .ok t => pure t
    | .error e => throw (IO.userError s!"{table}: {e}")
  let (value, pieces) ← match parseResult (← IO.FS.readFile result) with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"{result}: {e}")
  let header := (src.splitOn "\n").filter (·.startsWith "#") |>.map fun l => (l.drop 1).trimAscii.toString
  let n := lowerFirst name
  let rows := (List.range 30).map fun a =>
    "  " ++ String.intercalate ", " ((List.range 30).map fun b => toString (tbl.getD (a * 30 + b) 0))
  let pieceLits := pieces.map fun p => "[" ++ String.intercalate ", " (p.map toString) ++ "]"
  let w := s!"(fun a b => tableFn {n}Table a.val b.val)"
  IO.print <| String.intercalate "\n" ([
    "module",
    "public import Fern.Solver.Certificate",
    "",
    "/-!",
    s!"# Certificate: {name}",
    "",
    "Generated by `fern-solve cert`; do not edit. The count table's own header reads:",
    ""] ++ header.map ("    " ++ ·) ++ [
    "",
    s!"`{n}_upper` proves, by kernel evaluation and the standard axioms only, that some layout has",
    s!"same-finger weight {value} on this table.",
    "-/",
    "",
    "@[expose] public section",
    "",
    "namespace Fern.Solver.Data",
    "",
    "open Fern.Ortholinear Fern.Solver",
    "",
    "/-- Bigram counts: entry `30 * a + b` counts key `a` followed by key `b`. -/",
    s!"def {n}Table : List ℕ := [",
    String.intercalate ",\n" rows ++ "]",
    "",
    "/-- Pieces achieving the optimum found by `fern-solve solve`. Each piece is one finger. -/",
    s!"def {n}Pieces : List (List (Fin 30)) :=",
    "  [" ++ String.intercalate ",\n   " pieceLits ++ "]",
    "",
    s!"theorem {n}_check : checkPieces {w} {n}Pieces {value} = true := by",
    "  decide +kernel",
    "",
    s!"/-- Some layout has same-finger weight {value} on the table. -/",
    s!"theorem {n}_upper :",
    s!"    ∃ L : LayoutOn fullRepertoire, L.val.sfbWeight {w} = {value} :=",
    s!"  checkPieces_sound {n}_check",
    "",
    "end Fern.Solver.Data",
    ""])
  return 0

/-- Same-hand spacegram weight of a side and its complement, as `listSideCost` computes it. -/
def sideCostOf (tbl : Array Nat) (I J : List Nat) (simple C : List (List Nat)) : Nat :=
  let w (l : List Nat) := (l.map fun x => (l.map fun y => tbl.getD (x * 30 + y) 0).sum).sum
  w (I ++ C.flatten) + w (J ++ (simple.filter (· ∉ C)).flatten)

/-- A Lean module certifying the least same-hand spacegram weight among layouts with the pieces of
the `NAME` certificate. -/
def cmdTieCert (name : String) (table result : System.FilePath) : IO UInt32 := do
  let src ← IO.FS.readFile table
  let tbl ← match parseTable src with
    | .ok t => pure t
    | .error e => throw (IO.userError s!"{table}: {e}")
  let (_, pieces) ← match parseResult (← IO.FS.readFile result) with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"{result}: {e}")
  let I :: J :: simple := pieces
    | IO.eprintln "the result needs two index pieces first"; return 1
  let choices := simple.sublistsLen 3
  let some (value, best) := (choices.map fun C => (sideCostOf tbl I J simple C, C)).foldl
      (fun acc x => match acc with
        | none => some x
        | some a => if x.1 < a.1 then some x else some a) none
    | IO.eprintln "no choices"; return 1
  let total := totalOf tbl
  IO.eprintln s!"same-hand spacegram weight {value} of {total}; alternate-hand {total - value}"
  IO.eprintln s!"left hand: {pieceString I} {String.intercalate " " (best.map pieceString)}"
  IO.eprintln s!"right hand: {pieceString J} {String.intercalate " " ((simple.filter (· ∉ best)).map pieceString)}"
  let header := (src.splitOn "\n").filter (·.startsWith "#") |>.map fun l => (l.drop 1).trimAscii.toString
  let n := lowerFirst name
  let rows := (List.range 30).map fun a =>
    "  " ++ String.intercalate ", " ((List.range 30).map fun b => toString (tbl.getD (a * 30 + b) 0))
  let w := s!"(fun a b => tableFn {n}Spacegrams a.val b.val)"
  IO.print <| String.intercalate "\n" ([
    "module",
    s!"public import Fern.Solver.Data.{name}",
    "public import Fern.Solver.TieBreak",
    "",
    "/-!",
    s!"# Spacegram tie-break: {name}",
    "",
    "Generated by `fern-solve tiecert`; do not edit. The spacegram table's own header reads:",
    ""] ++ header.map ("    " ++ ·) ++ [
    "",
    s!"`{n}_sameHand` proves, by kernel evaluation and the standard axioms only, that {value} is the",
    s!"least same-hand spacegram weight over every layout with the pieces `{n}Pieces`.",
    "-/",
    "",
    "@[expose] public section",
    "",
    "namespace Fern.Solver.Data",
    "",
    "open Fern.Ortholinear Fern.Solver",
    "",
    "/-- Spacegram counts: entry `30 * a + b` counts key `a`, a space, then key `b`. -/",
    s!"def {n}Spacegrams : List ℕ := [",
    String.intercalate ",\n" rows ++ "]",
    "",
    s!"theorem {n}_tie : checkTieBreak {w} {n}Pieces {value} = true := by",
    "  decide +kernel",
    "",
    s!"/-- The least same-hand spacegram weight among layouts with the pieces is {value}. -/",
    s!"theorem {n}_sameHand :",
    s!"    IsLeast (Set.range fun L : \{L : LayoutOn fullRepertoire // L.val.columns = ({n}Pieces.map List.toFinset).toFinset} =>",
    s!"      L.val.val.sameHandWeight {w}) {value} :=",
    s!"  checkTieBreak_sound {n}_tie",
    "",
    "end Fern.Solver.Data",
    ""])
  return 0

def usage : String :=
  "usage:\n  fern-solve count [--skipgrams | --spacegrams] TEXT\n" ++
  "  fern-solve check TEXT TABLE\n  fern-solve solve TABLE > RESULT\n" ++
  "  fern-solve cert NAME TABLE RESULT > Fern/Solver/Data/NAME.lean\n" ++
  "  fern-solve tiecert NAME SPACEGRAMS RESULT > Fern/Solver/Data/NAMEHands.lean"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["count", text] => cmdCount "" text
  | ["count", kind, text] =>
    if kind == "--skipgrams" || kind == "--spacegrams" then cmdCount kind text
    else IO.eprintln usage; return 2
  | ["check", text, table] => cmdCheck text table
  | ["solve", table] => cmdSolve table
  | ["cert", name, table, result] => cmdCert name table result
  | ["tiecert", name, table, result] => cmdTieCert name table result
  | _ => IO.eprintln usage; return 2
