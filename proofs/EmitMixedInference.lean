import Jihoo.MixedInferenceExamples

def main : IO Unit := do
  match Jihoo.CoreBridge.Checked.generatedInferenceCases with
  | none => throw (IO.userError "inference fixture verdict, scope or serialization failure")
  | some source => IO.print source
