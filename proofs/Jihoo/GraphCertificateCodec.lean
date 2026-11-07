import Jihoo.GraphCertificates

/-! A canonical byte codec for the complete certificate datatype. The wire
alphabet is ASCII `0`, `1`, `;`. Natural numbers use little-endian binary followed
by `;`, with zero represented by `;` alone. This is not a proof about the JSON
adapter, operating-system IO, or the Jihoo importer. -/
namespace Jihoo.GraphCertificates.Canonical

abbrev Bytes := List UInt8
abbrev Parser (α : Type) := Bytes → Option (α × Bytes)

/-- Binary payload bytes, not abstract mathematical tokens. -/
def encodeNat (n : Nat) : Bytes :=
  if h : n = 0 then [59] else
    (if n % 2 = 0 then 48 else 49) :: encodeNat (n / 2)
termination_by n

def parseNat : Parser Nat
  | [] => none
  | b :: bs =>
      if b = 59 then some (0, bs)
      else if b = 48 then do
        let (n, rest) ← parseNat bs
        pure (2 * n, rest)
      else if b = 49 then do
        let (n, rest) ← parseNat bs
        pure (2 * n + 1, rest)
      else none

theorem parseNat_encode (n : Nat) (rest : Bytes) :
    parseNat (encodeNat n ++ rest) = some (n, rest) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      rw [encodeNat]
      split
      next hz => subst n; simp [parseNat]
      next hn =>
        have hi := ih (n / 2) (by omega)
        have hmod := Nat.mod_lt n (by omega : 0 < 2)
        split
        next he => simp [parseNat, hi]; omega
        next he => simp [parseNat, hi]; omega

def encodeMany (encode : α → Bytes) : List α → Bytes
  | [] => []
  | x :: xs => encode x ++ encodeMany encode xs

def parseMany (parse : Parser α) : Nat → Parser (List α)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
      let (x, bs) ← parse bs
      let (xs, bs) ← parseMany parse n bs
      pure (x :: xs, bs)

theorem parseMany_encode (encode : α → Bytes) (parse : Parser α)
    (law : ∀ x rest, parse (encode x ++ rest) = some (x, rest))
    (xs : List α) (rest : Bytes) :
    parseMany parse xs.length (encodeMany encode xs ++ rest) = some (xs, rest) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeMany, parseMany, List.append_assoc, law, ih]

def encodeList (encode : α → Bytes) (xs : List α) : Bytes :=
  encodeNat xs.length ++ encodeMany encode xs

def parseList (parse : Parser α) : Parser (List α) := fun bs => do
  let (count, bs) ← parseNat bs
  parseMany parse count bs

theorem parseList_encode (encode : α → Bytes) (parse : Parser α)
    (law : ∀ x rest, parse (encode x ++ rest) = some (x, rest))
    (xs : List α) (rest : Bytes) :
    parseList parse (encodeList encode xs ++ rest) = some (xs, rest) := by
  simp [parseList, encodeList, List.append_assoc, parseNat_encode,
    parseMany_encode encode parse law]

def encodeBool : Bool → Bytes
  | false => encodeNat 0
  | true => encodeNat 1

def parseBool : Parser Bool := fun bs => do
  let (n, bs) ← parseNat bs
  match n with
  | 0 => pure (false, bs)
  | 1 => pure (true, bs)
  | _ => none

theorem parseBool_encode (b : Bool) (rest : Bytes) :
    parseBool (encodeBool b ++ rest) = some (b, rest) := by
  cases b <;> simp [parseBool, encodeBool, parseNat_encode]

/-- Sign tag plus absolute magnitude; the negative sign with zero is rejected. -/
def encodeInt : Int → Bytes
  | .ofNat n => encodeNat 0 ++ encodeNat n
  | .negSucc n => encodeNat 1 ++ encodeNat (n + 1)

def parseInt : Parser Int := fun bs => do
  let (sign, bs) ← parseNat bs
  let (magnitude, bs) ← parseNat bs
  match sign, magnitude with
  | 0, n => pure (.ofNat n, bs)
  | 1, n + 1 => pure (.negSucc n, bs)
  | _, _ => none

theorem parseInt_encode (n : Int) (rest : Bytes) :
    parseInt (encodeInt n ++ rest) = some (n, rest) := by
  cases n <;> simp [parseInt, encodeInt, List.append_assoc, parseNat_encode]

def encodeNode : Node → Bytes
  | .var k => encodeNat 0 ++ encodeNat k
  | .natural n => encodeNat 1 ++ encodeNat n
  | .integer n => encodeNat 2 ++ encodeInt n
  | .u64 => encodeNat 3
  | .i64 => encodeNat 4
  | .array a => encodeNat 5 ++ encodeNat a
  | .lt a b => encodeNat 6 ++ encodeNat a ++ encodeNat b
  | .eq a b => encodeNat 7 ++ encodeNat a ++ encodeNat b
  | .pi e a b => encodeNat 8 ++ encodeBool e ++ encodeNat a ++ encodeNat b
  | .lam e a b => encodeNat 9 ++ encodeBool e ++ encodeNat a ++ encodeNat b
  | .app a b => encodeNat 10 ++ encodeNat a ++ encodeNat b
  | .elements xs => encodeNat 11 ++ encodeList encodeNat xs
  | .index a b c => encodeNat 12 ++ encodeNat a ++ encodeNat b ++ encodeNat c
  | .refl a => encodeNat 13 ++ encodeNat a
  | .zeroLe a => encodeNat 14 ++ encodeNat a
  | .decide a b => encodeNat 15 ++ encodeNat a ++ encodeNat b
  | .uadd a b => encodeNat 16 ++ encodeNat a ++ encodeNat b
  | .usub a b c => encodeNat 17 ++ encodeNat a ++ encodeNat b ++ encodeNat c

def parseNode : Parser Node := fun bs => do
  let (tag, bs) ← parseNat bs
  match tag with
  | 0 => let (a, bs) ← parseNat bs; pure (.var a, bs)
  | 1 => let (a, bs) ← parseNat bs; pure (.natural a, bs)
  | 2 => let (a, bs) ← parseInt bs; pure (.integer a, bs)
  | 3 => pure (.u64, bs)
  | 4 => pure (.i64, bs)
  | 5 => let (a, bs) ← parseNat bs; pure (.array a, bs)
  | 6 => let (a, bs) ← parseNat bs; let (b, bs) ← parseNat bs; pure (.lt a b, bs)
  | 7 => let (a, bs) ← parseNat bs; let (b, bs) ← parseNat bs; pure (.eq a b, bs)
  | 8 => let (e, bs) ← parseBool bs; let (a, bs) ← parseNat bs
         let (b, bs) ← parseNat bs; pure (.pi e a b, bs)
  | 9 => let (e, bs) ← parseBool bs; let (a, bs) ← parseNat bs
         let (b, bs) ← parseNat bs; pure (.lam e a b, bs)
  | 10 => let (a, bs) ← parseNat bs; let (b, bs) ← parseNat bs; pure (.app a b, bs)
  | 11 => let (a, bs) ← parseList parseNat bs; pure (.elements a, bs)
  | 12 => let (a, bs) ← parseNat bs; let (b, bs) ← parseNat bs
          let (c, bs) ← parseNat bs; pure (.index a b c, bs)
  | 13 => let (a, bs) ← parseNat bs; pure (.refl a, bs)
  | 14 => let (a, bs) ← parseNat bs; pure (.zeroLe a, bs)
  | 15 => let (a, bs) ← parseNat bs; let (b, bs) ← parseNat bs; pure (.decide a b, bs)
  | 16 => let (a, bs) ← parseNat bs; let (b, bs) ← parseNat bs; pure (.uadd a b, bs)
  | 17 => let (a, bs) ← parseNat bs; let (b, bs) ← parseNat bs
          let (c, bs) ← parseNat bs; pure (.usub a b c, bs)
  | _ => none

theorem parseNode_encode (n : Node) (rest : Bytes) :
    parseNode (encodeNode n ++ rest) = some (n, rest) := by
  cases n <;> simp [parseNode, encodeNode, List.append_assoc, parseNat_encode,
    parseBool_encode, parseInt_encode, parseList_encode encodeNat parseNat parseNat_encode]

def encodeGraph (g : Graph) : Bytes := encodeList encodeNode g.toList

def parseGraph : Parser Graph := fun bs => do
  let (nodes, bs) ← parseList parseNode bs
  pure (nodes.toArray, bs)

theorem parseGraph_encode (g : Graph) (rest : Bytes) :
    parseGraph (encodeGraph g ++ rest) = some (g, rest) := by
  simp [parseGraph, encodeGraph, parseList_encode encodeNode parseNode parseNode_encode]

def encodeOperation : Operation → Bytes
  | .shift n => encodeNat 0 ++ encodeNat n
  | .substitute n => encodeNat 1 ++ encodeNat n

def parseOperation : Parser Operation := fun bs => do
  let (tag, bs) ← parseNat bs
  let (n, bs) ← parseNat bs
  match tag with
  | 0 => pure (.shift n, bs)
  | 1 => pure (.substitute n, bs)
  | _ => none

theorem parseOperation_encode (op : Operation) (rest : Bytes) :
    parseOperation (encodeOperation op ++ rest) = some (op, rest) := by
  cases op <;> simp [parseOperation, encodeOperation, List.append_assoc, parseNat_encode]

/-- Version 1, input, output, operation, complete before graph, complete after graph. -/
def encodeCertificateList (c : Certificate) : Bytes :=
  encodeNat 1 ++ encodeNat c.input ++ encodeNat c.output ++
  encodeOperation c.operation ++ encodeGraph c.before ++ encodeGraph c.after

def parseCertificate : Parser Certificate := fun bs => do
  let (version, bs) ← parseNat bs
  if version ≠ 1 then none else do
    let (input, bs) ← parseNat bs
    let (output, bs) ← parseNat bs
    let (operation, bs) ← parseOperation bs
    let (before, bs) ← parseGraph bs
    let (after, bs) ← parseGraph bs
    pure ({ before, after, input, output, operation }, bs)

theorem parseCertificate_encode (c : Certificate) (rest : Bytes) :
    parseCertificate (encodeCertificateList c ++ rest) = some (c, rest) := by
  simp [parseCertificate, encodeCertificateList, List.append_assoc, parseNat_encode,
    parseOperation_encode, parseGraph_encode]

def encodeCertificate (c : Certificate) : ByteArray :=
  (encodeCertificateList c).toByteArray

/-- Complete consumption and exact re-encoding are mandatory. In particular,
nonminimal binary numerals and trailing bytes cannot alias a certificate. -/
def decodeCertificate (bytes : ByteArray) : Option Certificate := do
  let (c, []) ← parseCertificate bytes.data.toList | none
  if encodeCertificateList c = bytes.data.toList then some c else none

theorem decodeCertificate_encode (c : Certificate) :
    decodeCertificate (encodeCertificate c) = some c := by
  simp [decodeCertificate, encodeCertificate,
    show parseCertificate (encodeCertificateList c) = some (c, []) from
      by simpa using parseCertificate_encode c []]

theorem encodeCertificate_injective : Function.Injective encodeCertificate := by
  intro a b h
  have := congrArg decodeCertificate h
  simpa [decodeCertificate_encode] using this

theorem decodeCertificate_exact {bytes : ByteArray} {c : Certificate}
    (h : decodeCertificate bytes = some c) : encodeCertificate c = bytes := by
  unfold decodeCertificate at h
  cases hp : parseCertificate bytes.data.toList with
  | none => simp [hp] at h
  | some result =>
      rcases result with ⟨c', rest⟩
      cases rest with
      | cons b rest => simp [hp] at h
      | nil =>
          simp only [hp, bind, Option.bind] at h
          split at h
          next he =>
            cases h
            apply ByteArray.ext
            apply Array.ext'
            simpa [encodeCertificate, List.toList_data_toByteArray] using he
          next => contradiction

end Jihoo.GraphCertificates.Canonical
