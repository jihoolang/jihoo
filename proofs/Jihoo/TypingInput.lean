import Jihoo.TypingCertificateCodec

/-! Shared defensive IO/scanners. These resource checks and file operations are
outside the canonical codec and typing soundness theorems. -/
namespace Jihoo.GraphCertificates.TypingInput

def limit : Nat := 8 * 1024 * 1024

def readBounded (handle : IO.FS.Stream) : IO ByteArray := do
  let mut bytes := ByteArray.empty
  let mut eof := false
  while !eof do
    let chunk ← handle.read (min 65536 (limit + 1 - bytes.size)).toUSize
    if chunk.isEmpty then eof := true
    else
      bytes := bytes ++ chunk
      if bytes.size > limit then throw (IO.userError "file exceeds 8 MiB")
  return bytes

def input (args : List String) : IO ByteArray := do
  match args with
  | [] => readBounded (← IO.getStdin)
  | [path] =>
      let handle ← IO.FS.Handle.mk path .read
      readBounded (IO.FS.Stream.ofHandle handle)
  | _ => throw (IO.userError "expected stdin or one typing artifact path")

def scanNat (bytes : ByteArray) (start : Nat) : Option (Nat × Nat) := Id.run do
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

def scanFields (bytes : ByteArray) (start count : Nat) : Option Nat := do
  let mut cursor := start
  for _ in [:count] do
    let (_, next) ← scanNat bytes cursor
    cursor := next
  return cursor

def scanVector (bytes : ByteArray) (start bound : Nat) : Option Nat := do
  let (count, cursor) ← scanNat bytes start
  if count > bound then none else scanFields bytes cursor count

def scanNode (bytes : ByteArray) (start : Nat) : Option Nat := do
  let (tag, cursor) ← scanNat bytes start
  match tag with
  | 0 | 1 | 5 | 13 | 14 => scanFields bytes cursor 1
  | 2 | 6 | 7 | 10 | 15 | 16 => scanFields bytes cursor 2
  | 3 | 4 | 18 => return cursor
  | 8 | 9 | 12 | 17 => scanFields bytes cursor 3
  | 11 => scanVector bytes cursor nodeLimit
  | 19 =>
      let (level, cursor) ← scanNat bytes cursor
      if level < universeBound then some cursor else none
  | _ => none

def scanGraph (bytes : ByteArray) (start : Nat) : Option Nat := do
  let (count, start) ← scanNat bytes start
  if count > nodeLimit then none else do
    let mut cursor := start
    for _ in [:count] do
      cursor ← scanNode bytes cursor
    return cursor

def scanStep (bytes : ByteArray) (start : Nat) : Option Nat := do
  let cursor ← scanFields bytes start 1
  let cursor ← scanVector bytes cursor depthLimit
  let cursor ← scanFields bytes cursor 2
  scanVector bytes cursor Typing.stepLimit

def preflight (bytes : ByteArray) : Bool := (do
  let cursor ← scanFields bytes 0 5
  let cursor ← scanGraph bytes cursor
  let (count, start) ← scanNat bytes cursor
  if count > Typing.stepLimit then none else do
    let mut cursor := start
    for _ in [:count] do
      cursor ← scanStep bytes cursor
    if cursor = bytes.size then some () else none).isSome

def canonical (bytes : ByteArray) : IO Typing.Certificate := do
  unless preflight bytes do
    throw (IO.userError "invalid shape, token over 64 bits, or graph/derivation/vector count limit")
  let some certificate := Typing.Wire.decode bytes |
    throw (IO.userError "invalid or noncanonical typing artifact")
  return certificate

def canonicalSnapshot (bytes : ByteArray) : IO Typing.Wire.Snapshot := do
  let shape := do
    let cursor ← scanFields bytes 0 3
    let cursor ← scanGraph bytes cursor
    if cursor = bytes.size then some () else none
  unless shape.isSome do
    throw (IO.userError "invalid snapshot shape or bounds")
  let some snapshot := Typing.Wire.decodeSnapshot bytes |
    throw (IO.userError "invalid or noncanonical snapshot")
  return snapshot


end Jihoo.GraphCertificates.TypingInput
