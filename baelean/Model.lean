module
public import Mathlib.Data.Finset.Defs

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

/-- A key on the keyboard. -/
public structure Key where
  id : KeyId
  position : Position
  width : Rat  -- physical width in mm
  deriving DecidableEq, Repr, BEq, Hashable

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

/-- Extract the underlying key list from a Finset (unsafe but fine for display). -/
private unsafe def unsafeKeyList (kb : Keyboard) : List Key :=
  unsafeCast kb.keys.val

/-- Sort keys by row (y) then column (x). -/
private def sortKeys (keys : List Key) : List Key :=
  keys.mergeSort fun a b =>
    if a.position.y != b.position.y then decide (a.position.y < b.position.y)
    else decide (a.position.x < b.position.x)

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
private unsafe def reprKeyboardImpl (kb : Keyboard) : String :=
  let keys := sortKeys (unsafeKeyList kb)
  let rows := groupRows keys
  let charWidth := 5  -- characters per 1u
  let lines := rows.flatMap fun row =>
    let (border, content) := renderRow row charWidth
    [border, content]
  let lastRow := rows.getLast!
  let lastBorder := (renderRow lastRow charWidth).1
  let bottom := lastBorder.map fun c => if c == ',' || c == '.' then '\'' else c
  String.intercalate "\n" (lines ++ [bottom])

@[implemented_by reprKeyboardImpl]
public def reprKeyboard (kb : Keyboard) : String :=
  "Keyboard { ... }"

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
