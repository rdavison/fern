module
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Prod.Lex
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat

/-- Each physical finger used for typing. -/
public inductive Finger where
  | pinky
  | ring
  | middle
  | index
  | thumb
  deriving DecidableEq, Repr, BEq, Hashable

/-- Which hand a finger belongs to. -/
public inductive Hand where
  | left
  | right
  deriving DecidableEq, Repr, BEq, Hashable

/-- A physical position in 2D space (in millimetres). -/
public structure Position where
  x : Rat
  y : Rat
  deriving DecidableEq, Repr, BEq, Hashable

/-- Identifiers for every key that can appear on any keyboard. -/
public inductive KeyId where
  -- Alpha keys
  | a | b | c | d | e | f | g | h | i | j | k | l | m
  | n | o | p | q | r | s | t | u | v | w | x | y | z
  -- Number keys
  | n0 | n1 | n2 | n3 | n4 | n5 | n6 | n7 | n8 | n9
  -- Punctuation
  | grave | minus | equal | lbracket | rbracket | backslash
  | semicolon | apostrophe | comma | period | slash
  -- Modifiers
  | lshift | rshift | lctrl | rctrl | lalt | ralt | lsuper | rsuper
  -- Special keys
  | tab | caps | enter | backspace | space | menu
  | escape | insert | delete | home | end_ | pageUp | pageDown
  -- Arrow keys
  | up | down | left | right
  -- Function keys
  | f1 | f2 | f3 | f4 | f5 | f6 | f7 | f8 | f9 | f10 | f11 | f12
  deriving DecidableEq, Repr, BEq, Hashable

/-- Numeric encoding for ordering. -/
public def KeyId.toNat : KeyId → Nat
  | .a => 0 | .b => 1 | .c => 2 | .d => 3 | .e => 4
  | .f => 5 | .g => 6 | .h => 7 | .i => 8 | .j => 9
  | .k => 10 | .l => 11 | .m => 12 | .n => 13 | .o => 14
  | .p => 15 | .q => 16 | .r => 17 | .s => 18 | .t => 19
  | .u => 20 | .v => 21 | .w => 22 | .x => 23 | .y => 24
  | .z => 25
  | .n0 => 26 | .n1 => 27 | .n2 => 28 | .n3 => 29 | .n4 => 30
  | .n5 => 31 | .n6 => 32 | .n7 => 33 | .n8 => 34 | .n9 => 35
  | .grave => 36 | .minus => 37 | .equal => 38 | .lbracket => 39
  | .rbracket => 40 | .backslash => 41 | .semicolon => 42
  | .apostrophe => 43 | .comma => 44 | .period => 45 | .slash => 46
  | .lshift => 47 | .rshift => 48 | .lctrl => 49 | .rctrl => 50
  | .lalt => 51 | .ralt => 52 | .lsuper => 53 | .rsuper => 54
  | .tab => 55 | .caps => 56 | .enter => 57 | .backspace => 58
  | .space => 59 | .menu => 60
  | .escape => 61 | .insert => 62 | .delete => 63
  | .home => 64 | .end_ => 65 | .pageUp => 66 | .pageDown => 67
  | .up => 68 | .down => 69 | .left => 70 | .right => 71
  | .f1 => 72 | .f2 => 73 | .f3 => 74 | .f4 => 75
  | .f5 => 76 | .f6 => 77 | .f7 => 78 | .f8 => 79
  | .f9 => 80 | .f10 => 81 | .f11 => 82 | .f12 => 83

set_option maxHeartbeats 800000 in
public theorem KeyId.toNat_injective : Function.Injective KeyId.toNat := by
  intro a b h; cases a <;> cases b <;> first | rfl | (simp only [KeyId.toNat] at h; omega)

public instance : LinearOrder KeyId :=
  LinearOrder.lift' KeyId.toNat KeyId.toNat_injective

/-- A key on the keyboard. -/
public structure Key where
  id : KeyId
  position : Position
  width : Rat  -- physical width in mm
  deriving DecidableEq, Repr, BEq, Hashable

/-- Lexicographic ordering on keys by (y, x) then (width, id). -/
public def keyOrd (k : Key) : (Rat ×ₗ Rat) ×ₗ (Rat ×ₗ KeyId) :=
  toLex (toLex (k.position.y, k.position.x), toLex (k.width, k.id))

public theorem keyOrd_injective : Function.Injective keyOrd := by
  intro ⟨id1, ⟨x1, y1⟩, w1⟩ ⟨id2, ⟨x2, y2⟩, w2⟩ h
  simp only [keyOrd] at h
  obtain ⟨hpos, hrest⟩ := Prod.ext_iff.mp h
  obtain ⟨hy, hx⟩ := Prod.ext_iff.mp hpos
  obtain ⟨hw, hid⟩ := Prod.ext_iff.mp hrest
  subst hy; subst hx; subst hw; subst hid; rfl

public instance : LinearOrder Key :=
  LinearOrder.lift' keyOrd keyOrd_injective

/-- A keyboard, defined as a set of keys. -/
public structure Keyboard where
  keys : Finset Key

/-- Short label for a key identifier. -/
private def KeyId.label : KeyId → String
  | .a => "a" | .b => "b" | .c => "c" | .d => "d" | .e => "e"
  | .f => "f" | .g => "g" | .h => "h" | .i => "i" | .j => "j"
  | .k => "k" | .l => "l" | .m => "m" | .n => "n" | .o => "o"
  | .p => "p" | .q => "q" | .r => "r" | .s => "s" | .t => "t"
  | .u => "u" | .v => "v" | .w => "w" | .x => "x" | .y => "y"
  | .z => "z"
  | .n0 => "0" | .n1 => "1" | .n2 => "2" | .n3 => "3" | .n4 => "4"
  | .n5 => "5" | .n6 => "6" | .n7 => "7" | .n8 => "8" | .n9 => "9"
  | .grave => "~" | .minus => "-" | .equal => "=" | .lbracket => "["
  | .rbracket => "]" | .backslash => "\\" | .semicolon => ";"
  | .apostrophe => "'" | .comma => "," | .period => "." | .slash => "/"
  | .lshift => "lsh" | .rshift => "rsh" | .lctrl => "lct" | .rctrl => "rct"
  | .lalt => "lal" | .ralt => "ral" | .lsuper => "sup" | .rsuper => "sup"
  | .tab => "tab" | .caps => "cap" | .enter => "ret" | .backspace => "bks"
  | .space => "spc" | .menu => "mnu"
  | .escape => "esc" | .insert => "ins" | .delete => "del"
  | .home => "hom" | .end_ => "end" | .pageUp => "pgu" | .pageDown => "pgd"
  | .up => "up" | .down => "dn" | .left => "lt" | .right => "rt"
  | .f1 => "f1" | .f2 => "f2" | .f3 => "f3" | .f4 => "f4"
  | .f5 => "f5" | .f6 => "f6" | .f7 => "f7" | .f8 => "f8"
  | .f9 => "f9" | .f10 => "f10" | .f11 => "f11" | .f12 => "f12"

/-- Group a sorted key list into rows (keys sharing the same y coordinate). -/
private def groupRows (keys : List Key) : List (List Key) :=
  keys.foldl (fun acc k =>
    match acc with
    | [] => [[k]]
    | row :: rest =>
      match row.head? with
      | some h =>
        if h.position.y == k.position.y then (row ++ [k]) :: rest
        else [k] :: row :: rest
      | none => [k] :: row :: rest
  ) [] |>.reverse

/-- Pad or truncate a string to exactly n characters, centered. -/
private def centerPad (s : String) (n : Nat) : String :=
  if s.length >= n then (s.take n).toString
  else
    let pad := n - s.length
    let lpad := pad / 2
    let rpad := pad - lpad
    String.ofList (List.replicate lpad ' ') ++ s ++ String.ofList (List.replicate rpad ' ')

/-- Render a single row of keys as a bordered ASCII line.
    charWidth is how many characters correspond to 1u. -/
private def renderRow (row : List Key) (charWidth : Nat) : String × String :=
  let u : Rat := 19050 / 1000
  let (cells, _) := row.foldl (fun (acc : List (String × String) × Rat) k =>
    let cumEnd := acc.2 + k.width / u * (charWidth : Rat)
    let w := cumEnd.floor.toNat - acc.2.floor.toNat
    let inner := if w > 0 then w - 1 else 0
    (acc.1 ++ [(centerPad k.id.label inner, String.ofList (List.replicate inner '-'))], cumEnd)
  ) ([], 0)
  let border := "," ++ String.intercalate "," (cells.map (·.2)) ++ "."
  let content := "|" ++ String.intercalate "|" (cells.map (·.1)) ++ "|"
  (border, content)

/-- Render a keyboard as ASCII art. -/
public def reprKeyboard (kb : Keyboard) : String :=
  let keys := kb.keys.sort
  let rows := groupRows keys
  let charWidth := 5  -- characters per 1u
  let lines := rows.flatMap fun row =>
    let (border, content) := renderRow row charWidth
    [border, content]
  match rows.getLast? with
  | some lastRow =>
    let lastBorder := (renderRow lastRow charWidth).1
    let bottom := lastBorder.map fun c => if c == ',' || c == '.' then '\'' else c
    String.intercalate "\n" (lines ++ [bottom])
  | none => ""

public instance : Repr Keyboard where
  reprPrec kb _ := reprKeyboard kb

public instance : BEq Keyboard where
  beq a b := a.keys == b.keys

/-- 1u in mm. Standard key unit spacing. -/
private def u : Rat := 19050 / 1000

/-- Build keys from a flat list of (id, width-in-u) pairs arranged in rows.
    Each key is centered within its width, rows are spaced 1u apart. -/
private def rowKeys (rows : List (List (KeyId × Rat))) : List Key :=
  (List.range rows.length |>.zip rows).flatMap fun ⟨rowIdx, entries⟩ =>
    let y := ↑rowIdx * u
    (entries.foldl (fun (acc : List Key × Rat) ⟨id, w⟩ =>
      let x := acc.2 + w * u / 2
      (acc.1 ++ [⟨id, ⟨x, y⟩, w * u⟩], acc.2 + w * u)
    ) ([], 0)).1

/-- A 3×10 ortholinear keyboard with 1u spacing (19.05mm).
    Uses the 30 alpha keys (q-p, a-l, z-m) as key identifiers. -/
public def Ortho3x10 : Keyboard where
  keys := ⟨Quot.mk _ (rowKeys [
    [(.q,1), (.w,1), (.e,1), (.r,1), (.t,1), (.y,1), (.u,1), (.i,1), (.o,1), (.p,1)],
    [(.a,1), (.s,1), (.d,1), (.f,1), (.g,1), (.h,1), (.j,1), (.k,1), (.l,1), (.semicolon,1)],
    [(.z,1), (.x,1), (.c,1), (.v,1), (.b,1), (.n,1), (.m,1), (.comma,1), (.period,1), (.slash,1)]
  ]), by native_decide⟩

/-- Standard ANSI physical layout (key positions and widths only). -/
public def ANSI : Keyboard where
  keys := ⟨Quot.mk _ (rowKeys [
    -- Number row
    [(.grave,1), (.n1,1), (.n2,1), (.n3,1), (.n4,1), (.n5,1), (.n6,1), (.n7,1), (.n8,1), (.n9,1), (.n0,1), (.minus,1), (.equal,1), (.backspace,2)],
    -- Top alpha
    [(.tab,3/2), (.q,1), (.w,1), (.e,1), (.r,1), (.t,1), (.y,1), (.u,1), (.i,1), (.o,1), (.p,1), (.lbracket,1), (.rbracket,1), (.backslash,3/2)],
    -- Home row
    [(.caps,7/4), (.a,1), (.s,1), (.d,1), (.f,1), (.g,1), (.h,1), (.j,1), (.k,1), (.l,1), (.semicolon,1), (.apostrophe,1), (.enter,9/4)],
    -- Bottom alpha
    [(.lshift,9/4), (.z,1), (.x,1), (.c,1), (.v,1), (.b,1), (.n,1), (.m,1), (.comma,1), (.period,1), (.slash,1), (.rshift,11/4)],
    -- Bottom
    [(.lctrl,5/4), (.lsuper,5/4), (.lalt,5/4), (.space,25/4), (.ralt,5/4), (.rsuper,5/4), (.menu,5/4), (.rctrl,5/4)]
  ]), by native_decide⟩

def foo := let a := Nat; fun x : a => x + 2
def bar : Nat → Nat := fun x => x + 2

/-- All larger projects are a political place;
    if you can't play the politics, it doesn't matter whether you are right or wrong. -/
theorem office_politics
    (Project Person : Type)
    (isLarger isPolitical : Project → Prop)
    (canPlayPolitics : Person → Project → Prop)
    (correctnessMatters : Person → Project → Prop)
    (larger_projects_are_political : ∀ p, isLarger p → isPolitical p)
    (politics_trumps_correctness : ∀ person project,
      isPolitical project → ¬canPlayPolitics person project → ¬correctnessMatters person project)
    (project : Project) (person : Person)
    (hLarger : isLarger project)
    (hCantPlay : ¬canPlayPolitics person project)
    : ¬correctnessMatters person project :=
  politics_trumps_correctness person project
    (larger_projects_are_political project hLarger)
    hCantPlay
