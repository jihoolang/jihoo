import Jihoo.GraphCertificateReplay
import Jihoo.GraphCertificateJson

/-! IO, resource guards, and the legacy JSON seeding adapter are outside the
codec/replay theorems. Canonical decoding and chain validation use their proved
pure implementations. No compiler is invoked by this checker. -/
open Jihoo.GraphCertificates

private def limit : Nat := 8 * 1024 * 1024

private def readBounded (handle : IO.FS.Stream) : IO ByteArray := do
  let mut bytes := ByteArray.empty
  let mut eof := false
  while !eof do
    let chunk ← handle.read (min 65536 (limit + 1 - bytes.size)).toUSize
    if chunk.isEmpty then eof := true
    else
      bytes := bytes ++ chunk
      if bytes.size > limit then throw (IO.userError "file exceeds 8 MiB")
  return bytes

private def input (args : List String) : IO ByteArray := do
  match args with
  | [] => readBounded (← IO.getStdin)
  | [path] =>
      let handle ← IO.FS.Handle.mk path .read
      readBounded (IO.FS.Stream.ofHandle handle)
  | _ => throw (IO.userError "expected stdin or one artifact path")

/-- Defensive indexed scan; rejects long numbers before constructing a Nat.
The generic proved codec remains total and unbounded. -/
private def scanNat (bytes : ByteArray) (start : Nat) : Option (Nat × Nat) := Id.run do
  let mut n := 0
  let mut weight := 1
  for i in [start:min bytes.size (start + 65)] do
    let byte := bytes[i]!
    if byte == 59 then return some (n, i + 1)
    if i == start + 64 then return none
    if byte == 49 then n := n + weight
    else if byte != 48 then return none
    weight := weight * 2
  return none

private def scanFields (bytes : ByteArray) (start count : Nat) : Option Nat := do
  let mut cursor := start
  for _ in [:count] do
    let (_, next) ← scanNat bytes cursor
    cursor := next
  return cursor

private def scanNode (bytes : ByteArray) (start : Nat) : Option Nat := do
  let (tag, cursor) ← scanNat bytes start
  match tag with
  | 0 | 1 | 5 | 13 | 14 => scanFields bytes cursor 1
  | 2 | 6 | 7 | 10 | 15 | 16 => scanFields bytes cursor 2
  | 3 | 4 => return cursor
  | 8 | 9 | 12 | 17 => scanFields bytes cursor 3
  | 11 =>
      let (count, cursor) ← scanNat bytes cursor
      if count > nodeLimit then none else scanFields bytes cursor count
  | _ => none

private def scanGraph (bytes : ByteArray) (start : Nat) : Option Nat := do
  let (count, start) ← scanNat bytes start
  if count > nodeLimit then none else do
    let mut cursor := start
    for _ in [:count] do
      cursor ← scanNode bytes cursor
    return cursor

/-- Both graph counts and every element-vector count are capped before the
recursive canonical parser runs. No input bytes are normalized or repaired. -/
private def preflight (bytes : ByteArray) : IO Unit := do
  let result := do
    let cursor ← scanFields bytes 0 5
    let cursor ← scanGraph bytes cursor
    let cursor ← scanGraph bytes cursor
    if cursor = bytes.size then some () else none
  unless result.isSome do
    throw (IO.userError "invalid canonical shape, token over 64 bits, or graph/child count over 4096")

private def canonical (bytes : ByteArray) : IO Certificate := do
  preflight bytes
  let some c := Canonical.decodeCertificate bytes |
    throw (IO.userError "invalid or noncanonical artifact encoding")
  return c

private def checked (c : Certificate) : IO Unit := do
  unless validate c do
    throw (IO.userError "invalid graph, append-only relation, bounds, or transformation")

private def splitChain (bytes : ByteArray) : IO (ByteArray × ByteArray) := do
  let parts := bytes.data.toList.splitOn 10
  let [previous, next] := parts |
    throw (IO.userError "expected exactly two canonical artifacts separated by one newline")
  return (previous.toByteArray, next.toByteArray)

private def request (args : List String) : IO (Option Operation) := do
  match args with
  | [] => return none
  | ["shift", amount] =>
      let some n := amount.toNat? | throw (IO.userError "invalid requested shift amount")
      if n ≥ Jihoo.CoreBridge.signedBound.toNat then
        throw (IO.userError "requested shift exceeds signed i64")
      return some (.shift n)
  | ["substitute", replacement] =>
      let some n := replacement.toNat? | throw (IO.userError "invalid requested replacement")
      if n ≥ idBound then throw (IO.userError "requested replacement exceeds identifier bound")
      return some (.substitute n)
  | _ => throw (IO.userError "expected --chain [shift AMOUNT | substitute REPLACEMENT]")

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | mode :: rest =>
        if mode == "--json-input" || mode == "--json" then
          let bytes ← input rest
          let some text := String.fromUTF8? bytes | throw (IO.userError "invalid UTF-8")
          let c ← match JsonAdapter.parse text with
            | .ok c => pure c
            | .error message => throw (IO.userError message)
          checked c
          let out ← IO.getStdout
          out.write (Canonical.encodeCertificate c)
          out.flush
        else if mode == "--chain" then
          let requested ← request rest
          let (previousBytes, nextBytes) ← splitChain (← input [])
          let previous ← canonical previousBytes
          let next ← canonical nextBytes
          match requested with
          | none =>
              unless validateChain previous [next] do
                throw (IO.userError "invalid chain or graph/root continuity")
          | some operation =>
              unless Canonical.validateReplay previousBytes nextBytes operation do
                throw (IO.userError "invalid chain, graph/root continuity, or requested operation")
          IO.println "canonical artifact chain accepted"
        else
          let c ← canonical (← input args)
          checked c
          IO.println "canonical artifact accepted"
    | [] =>
        let c ← canonical (← input [])
        checked c
        IO.println "canonical artifact accepted"
    return 0
  catch error =>
    IO.eprintln s!"canonical artifact rejected: {error}"
    return 1
