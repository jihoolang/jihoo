import Jihoo.CoreBridgeExamples

def main : IO Unit := do
  match Jihoo.CoreBridge.generatedProgram with
  | none => throw (IO.userError "core bridge fixture exceeded serializer scope or fuel")
  | some source => IO.print source
