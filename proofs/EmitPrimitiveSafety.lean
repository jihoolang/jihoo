import Jihoo.CorePrimitiveExamples

def main : IO Unit := do
  match Jihoo.CoreBridge.Raw.Beta.PrimitiveExamples.program with
  | none => throw (IO.userError "primitive fixture serializer exceeded scope or fuel")
  | some source => IO.print source
