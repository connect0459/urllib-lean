namespace Urllib.Host

structure Ipv4 where
  value : UInt32
  deriving DecidableEq, Repr

inductive Ipv4Error where
  | nonNumericPart
  | tooManyParts
  | outOfRange
  deriving DecidableEq, Repr

namespace Ipv4

def digitValue? (radix : Nat) (c : Char) : Option Nat :=
  let value :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 0x30)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 0x61 + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 0x41 + 10)
    else none
  value.filter (· < radix)

def numberIn (radix : Nat) (digits : List Char) : Option Nat :=
  digits.foldlM (fun acc c => (digitValue? radix c).map (acc * radix + ·)) 0

def parseNumber? (input : String) : Option Nat :=
  match input.toList with
  | [] => none
  | '0' :: x :: rest =>
    if x = 'x' ∨ x = 'X' then numberIn 16 rest else numberIn 8 (x :: rest)
  | digits => numberIn 10 digits

def splitParts (input : String) : List String :=
  let parts := input.splitOn "."
  match parts.getLast? with
  | some "" => if parts.length > 1 then parts.dropLast else parts
  | _ => parts

def parse (input : String) : Except Ipv4Error Ipv4 := do
  let parts := splitParts input
  if parts.length > 4 then throw .tooManyParts
  let numbers ←
    match parts.mapM parseNumber? with
    | some numbers => pure numbers
    | none => throw .nonNumericPart
  match numbers.getLast? with
  | none => throw .nonNumericPart
  | some last =>
    let leading := numbers.dropLast
    if leading.any (· > 255) then throw .outOfRange
    if last ≥ 256 ^ (5 - numbers.length) then throw .outOfRange
    let value := leading.zipIdx.foldl (fun acc (n, i) => acc + n * 256 ^ (3 - i)) last
    return ⟨UInt32.ofNat value⟩

def serialize (address : Ipv4) : String :=
  let n := address.value.toNat
  String.intercalate "." ([n / 2 ^ 24 % 256, n / 2 ^ 16 % 256, n / 2 ^ 8 % 256, n % 256].map toString)

def lastLabelIsNumber (label : String) : Bool :=
  (!label.isEmpty && label.all Char.isDigit) || (parseNumber? label).isSome

def endsInNumber (input : String) : Bool :=
  let parts := input.splitOn "."
  match parts.getLast? with
  | none => false
  | some last =>
    if last.isEmpty then
      if parts.length = 1 then false
      else
        match parts.dropLast.getLast? with
        | some label => lastLabelIsNumber label
        | none => false
    else
      lastLabelIsNumber last

end Ipv4

end Urllib.Host
