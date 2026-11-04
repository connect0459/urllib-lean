namespace Urllib.Host

/-- An IPv4 address as a 32-bit unsigned integer. -/
structure Ipv4 where
  /-- The address, most significant octet first. -/
  value : UInt32
  deriving DecidableEq, Repr

/-- Reasons why the IPv4 parser rejects its input. -/
inductive Ipv4Error where
  /-- A part is empty or is not a decimal, octal, or hexadecimal number. -/
  | nonNumericPart
  /-- The input has more than four parts. -/
  | tooManyParts
  /-- A part exceeds the range its position allows. -/
  | outOfRange
  deriving DecidableEq, Repr

namespace Ipv4

/-- The value of `c` as a digit in `radix`; `none` when `c` is not such a digit. -/
def digitValue? (radix : Nat) (c : Char) : Option Nat :=
  let value :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 0x30)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 0x61 + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 0x41 + 10)
    else none
  value.filter (· < radix)

/-- The value of `digits` in `radix`; `none` when a character is not a digit of that radix. -/
def numberIn (radix : Nat) (digits : List Char) : Option Nat :=
  digits.foldlM (fun acc c => (digitValue? radix c).map (acc * radix + ·)) 0

/-- The IPv4 number parser: a `0x` or `0X` prefix selects hexadecimal, a leading `0` octal, otherwise decimal; `none` on failure. -/
def parseNumber? (input : List Char) : Option Nat :=
  match input with
  | [] => none
  | '0' :: x :: rest =>
    if x = 'x' ∨ x = 'X' then numberIn 16 rest else numberIn 8 (x :: rest)
  | digits => numberIn 10 digits

/-- Splits at every `.`; the result always has at least one part. -/
def splitDots : List Char → List (List Char)
  | [] => [[]]
  | c :: rest =>
    match splitDots rest with
    | part :: more => if c = '.' then [] :: part :: more else (c :: part) :: more
    | [] => [[]]

/-- Splits at dots and drops one trailing empty part. -/
def splitParts (chars : List Char) : List (List Char) :=
  let parts := splitDots chars
  match parts.getLast? with
  | some [] => if parts.length > 1 then parts.dropLast else parts
  | _ => parts

/-- The IPv4 parser on characters. -/
def parseChars (chars : List Char) : Except Ipv4Error Ipv4 := do
  let parts := splitParts chars
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

/-- The IPv4 parser of the URL Standard. -/
def parse (input : String) : Except Ipv4Error Ipv4 :=
  parseChars input.toList

/-- The characters of the dotted decimal form. -/
def serializeChars (address : Ipv4) : List Char :=
  let n := address.value.toNat
  let part (k : Nat) : List Char := Nat.toDigits 10 (n / 2 ^ k % 256)
  part 24 ++ '.' :: (part 16 ++ '.' :: (part 8 ++ '.' :: part 0))

/-- The dotted decimal form of an address. -/
def serialize (address : Ipv4) : String :=
  String.ofList (serializeChars address)

/-- Whether a label is all decimal digits or parses as an IPv4 number. -/
def lastLabelIsNumber (label : List Char) : Bool :=
  (!label.isEmpty && label.all Char.isDigit) || (parseNumber? label).isSome

/-- The "ends in a number" checker of the URL Standard. -/
def endsInNumber (input : String) : Bool :=
  let parts := splitDots input.toList
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
