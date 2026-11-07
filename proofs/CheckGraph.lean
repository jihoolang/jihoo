import Jihoo.GraphCertificateJson

/-! IO and JSON parsing are outside the graph-validation theorem. This command
checks one bounded snapshot file and deliberately never invokes a compiler. -/
def main (args : List String) : IO UInt32 := do
  try
    let [path] := args | throw (IO.userError "expected one certificate path")
    let handle ← IO.FS.Handle.mk path .read
    let limit := 8 * 1024 * 1024
    let mut bytes := ByteArray.empty
    let mut eof := false
    while !eof do
      let chunk ← handle.read (min 65536 (limit + 1 - bytes.size)).toUSize
      if chunk.isEmpty then
        eof := true
      else
        bytes := bytes ++ chunk
        if bytes.size > limit then throw (IO.userError "file exceeds 8 MiB")
    let some text := String.fromUTF8? bytes | throw (IO.userError "invalid UTF-8")
    match Jihoo.GraphCertificates.JsonAdapter.parse text with
    | .error message => throw (IO.userError message)
    | .ok certificate =>
        if Jihoo.GraphCertificates.validate certificate then
          IO.println "graph certificate accepted"
          return 0
        else throw (IO.userError "invalid graph, append-only relation, bounds, or transformation")
  catch error =>
    IO.eprintln s!"graph certificate rejected: {error}"
    return 1
