namespace Urllib.Unicode

/-- A closed range of code points carrying a value. -/
structure Range (α : Type) where
  /-- The first code point of the range. -/
  low : Nat
  /-- The last code point of the range. -/
  high : Nat
  /-- The value shared by every code point of the range. -/
  value : α

/-- The value of a hexadecimal digit. -/
def hexDigitValue? (c : Char) : Option Nat :=
  let n := c.toNat
  if n < 48 then none
  else if n < 58 then some (n - 48)
  else if n < 65 then none
  else if n < 71 then some (n - 55)
  else if n < 97 then none
  else if n < 103 then some (n - 87)
  else none

/-- Parses a non-empty hexadecimal numeral. -/
def parseHex (s : String) : Option Nat :=
  if s.isEmpty then none
  else s.toList.foldlM (fun acc c => (hexDigitValue? c).map (acc * 16 + ·)) 0

/-- Parses a line `low high payload...` of a generated table; the payload is decoded by `decode`. -/
def parseRange {α : Type} (decode : List String → Option α) (line : String) : Option (Range α) :=
  match line.splitOn " " with
  | low :: high :: rest => do
    let low ← parseHex low
    let high ← parseHex high
    let value ← decode rest
    some { low, high, value }
  | _ => none

/-- Parses a generated table: one range per line, in ascending order; malformed lines are skipped. -/
def parseTable {α : Type} (decode : List String → Option α) (raw : String) : Array (Range α) :=
  (raw.splitOn "\n").filterMap (parseRange decode) |>.toArray

/-- The value of the range containing `cp`, found by binary search in an ascending table. -/
def lookup? {α : Type} (table : Array (Range α)) (cp : Nat) : Option α :=
  go 0 table.size (Nat.le_refl _)
where
  go (low high : Nat) (bound : high ≤ table.size) : Option α :=
    if _h : low < high then
      let mid := (low + high) / 2
      let r := table[mid]'(by omega)
      if cp < r.low then go low mid (by omega)
      else if r.high < cp then go (mid + 1) high bound
      else some r.value
    else none
  termination_by high - low

/-- Decodes an empty payload. -/
def decodeUnit (fields : List String) : Option Unit :=
  if fields.isEmpty then some () else none

/-- Decodes a payload of one decimal number. -/
def decodeNat (fields : List String) : Option Nat :=
  match fields with
  | [value] => value.toNat?
  | _ => none

/-- Decodes a payload of one word. -/
def decodeName (fields : List String) : Option String :=
  match fields with
  | [name] => some name
  | _ => none

end Urllib.Unicode
