import Jihoo.MixedTelescopeBridgeExamples

def main : IO Unit := do
  match Jihoo.CoreBridge.MixedBridge.generatedMixedProgram with
  | none => throw (IO.userError "mixed telescope serializer exceeded scope or fuel")
  | some text => IO.print text
