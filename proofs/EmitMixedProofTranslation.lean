import Jihoo.MixedProofTranslationExamples

def main : IO Unit := do
  match Jihoo.MixedProofFunctions.Bridge.generatedProgram with
  | none => throw (IO.userError "mixed proof translation serialization exceeded scope/fuel")
  | some source => IO.print source
