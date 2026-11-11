import Jihoo.NativeCompositionMirSnapshot
import Jihoo.NativeCompositionMirCorrespondence
import Jihoo.TypingInput
import Jihoo.GraphCertificateJson
import Jihoo.MirFixtureAdmission

/-! Test adapter for one fixed parametric theorem association. No sample runtime
inputs are accepted. Complete JSON structural equality binds the native source
and MIR snapshots to the retained formal fixtures. Parsing/export fidelity is
trusted, not a general compiler-refinement theorem. -/
def main (args : List String) : IO UInt32 := do
  try
    unless args.isEmpty do throw (IO.userError "stdin only")
    let bytes ← Jihoo.GraphCertificates.TypingInput.readBounded (← IO.getStdin)
    let some text := String.fromUTF8? bytes | throw (IO.userError "invalid UTF8")
    match Jihoo.MirFixtureAdmission.check Jihoo.NativeCompositionMirSnapshot.expected text with
    | .error e => throw (IO.userError e)
    | .ok _ => IO.println "native-composition-mir accepted"; return 0
  catch e => IO.eprintln s!"native-composition-mir rejected: {e}"; return 1
