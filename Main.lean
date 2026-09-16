import Fern

def main : IO Unit := do
  IO.println (repr Ortho3x10).pretty
  IO.println ""
  IO.println (repr ANSI).pretty
