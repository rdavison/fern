module

/-- Single characters. -/
public def unigrams (chars : List Char) : List String :=
  chars.map fun c => String.ofList [c]

/-- Consecutive pairs: ab, bc, cd, ... -/
public def bigrams (chars : List Char) : List String :=
  match chars with
  | a :: b :: rest => String.ofList [a, b] :: bigrams (b :: rest)
  | _ => []

/-- Consecutive triples: abc, bcd, cde, ... -/
public def trigrams (chars : List Char) : List String :=
  match chars with
  | a :: b :: c :: rest => String.ofList [a, b, c] :: trigrams (b :: c :: rest)
  | _ => []

/-- Pairs with one skipped between: a_c, b_d, c_e ...
    Captures same-finger usage even with an intervening key. -/
public def skipgrams (chars : List Char) : List String :=
  match chars with
  | a :: b :: c :: rest => String.ofList [a, c] :: skipgrams (b :: c :: rest)
  | _ => []

/-- ABA patterns where the first and third characters are the same.
    Detects alternation between two keys. -/
public def trills (chars : List Char) : List String :=
  match chars with
  | a :: b :: c :: rest =>
    let next := trills (b :: c :: rest)
    if a == c then String.ofList [a, b] :: next
    else next
  | _ => []
