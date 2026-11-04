namespace Urllib.Punycode

/-- Reasons why `decode` rejects its input. -/
inductive DecodeError where
  /-- A code point at or above 128 appears before the last delimiter. -/
  | nonBasicCodePoint
  /-- A character of the extension is not a base-36 digit. -/
  | invalidDigit
  /-- The input ends in the middle of a variable-length integer. -/
  | truncated
  /-- A decoded value is not a Unicode scalar value. -/
  | invalidCodePoint
  deriving Repr, DecidableEq

/-- The base of the variable-length integers (RFC 3492, section 5). -/
def base : Nat := 36
/-- The smallest threshold of a digit position. -/
def tMin : Nat := 1
/-- The largest threshold of a digit position. -/
def tMax : Nat := 26
/-- The skew parameter of the bias adaptation. -/
def skew : Nat := 38
/-- The damping factor applied to the first delta of the bias adaptation. -/
def damp : Nat := 700
/-- The bias at the start of encoding and decoding. -/
def initialBias : Nat := 72
/-- The first non-basic code point value considered by the algorithm. -/
def initialN : Nat := 128
/-- The delimiter between the basic code points and the extension. -/
def delimiter : Char := '-'

/-- The threshold of the digit at position `k` for the current `bias`, clamped to `[tMin, tMax]`. -/
def threshold (k bias : Nat) : Nat :=
  if k ≤ bias then tMin
  else if k ≥ bias + tMax then tMax
  else k - bias

theorem one_le_threshold (k bias : Nat) : 1 ≤ threshold k bias := by
  unfold threshold tMin tMax
  split <;> (try split) <;> omega

theorem threshold_le (k bias : Nat) : threshold k bias ≤ 26 := by
  unfold threshold tMin tMax
  split <;> (try split) <;> omega

/-- Scales `delta` down by `base - tMin` while it is large, accumulating the digit position `k`. -/
def adaptLoop (delta k : Nat) : Nat :=
  if delta > ((base - tMin) * tMax) / 2 then
    adaptLoop (delta / (base - tMin)) (k + base)
  else
    k + (base - tMin + 1) * delta / (delta + skew)
termination_by delta
decreasing_by
  unfold base tMin tMax at *
  omega

/-- The bias adaptation function (RFC 3492, section 6.1). -/
def adapt (delta numPoints : Nat) (firstTime : Bool) : Nat :=
  let delta := if firstTime then delta / damp else delta / 2
  adaptLoop (delta + delta / numPoints) 0

/-- Maps a digit in `0..35` to its lowercase basic code point (`a`-`z`, then `0`-`9`). -/
def digitToChar (d : Nat) : Char :=
  if d < 26 then Char.ofNat (97 + d) else Char.ofNat (22 + d)

/-- Maps a basic code point to its digit in either letter case; `none` for any other character. -/
def charToDigit? (c : Char) : Option Nat :=
  if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat - 65)
  else if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat - 97)
  else if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48 + 26)
  else none

/-- Encodes `q` as a generalized variable-length integer, starting at digit position `k` under `bias`. -/
def encodeIntegerFrom (bias k q : Nat) : List Char :=
  if q < threshold k bias then
    [digitToChar q]
  else
    digitToChar (threshold k bias + (q - threshold k bias) % (base - threshold k bias)) ::
      encodeIntegerFrom bias (k + base) ((q - threshold k bias) / (base - threshold k bias))
termination_by q
decreasing_by
  have h1 := one_le_threshold k bias
  have h2 := threshold_le k bias
  unfold base
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)

/-- Inserts `x` into `xs` at index `i`. -/
def insertAt {α : Type} (xs : List α) (i : Nat) (x : α) : List α :=
  xs.take i ++ x :: xs.drop i

/-- The index at which `item` enters `current`: the number of present items that originally precede it. -/
def insertionPosition (current : List (Nat × Nat)) (item : Nat × Nat) : Nat :=
  (current.filter (fun x => decide (x.2 < item.2))).length

/-- Orders (code point, original position) pairs by code point, then by original position. -/
def itemLe (a b : Nat × Nat) : Bool :=
  decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2))

/-- Encodes an insertion plan: for each item, emits the delta from the previous insertion as a variable-length integer and adapts the bias. -/
def encodeInsertions : List (Nat × Nat) → Nat → Nat → Nat → List (Nat × Nat) → List Char
  | _, _, _, _, [] => []
  | current, n, i, bias, item :: rest =>
    let size := current.length + 1
    let position := insertionPosition current item
    let delta := (item.1 - n) * size + position - i
    encodeIntegerFrom bias base delta ++
      encodeInsertions (insertAt current position item) item.1 (position + 1)
        (adapt delta size (i == 0)) rest

/-- The basic code points of the input paired with their original positions. -/
def basicItems (codePoints : List Nat) : List (Nat × Nat) :=
  codePoints.zipIdx.filter (fun x => decide (x.1 < 128))

/-- The insertion plan: the non-basic code points paired with their original positions, sorted by `itemLe`. -/
def planOf (codePoints : List Nat) : List (Nat × Nat) :=
  (codePoints.zipIdx.filter (fun x => decide (128 ≤ x.1))).mergeSort (fun a b => itemLe a b)

/-- Encodes a string as Punycode (RFC 3492). The function is total, its output is ASCII, and `decode` inverts it. -/
def encode (input : String) : String :=
  let codePoints := input.toList.map Char.toNat
  let basic := basicItems codePoints
  let basicPrefix :=
    if basic.isEmpty then [] else basic.map (fun x => Char.ofNat x.1) ++ [delimiter]
  String.ofList (basicPrefix ++ encodeInsertions basic initialN 0 initialBias (planOf codePoints))

/-- Decodes a generalized variable-length integer, returning the updated value and the remaining characters. -/
def decodeInteger (bias : Nat) : List Char → Nat → Nat → Nat → Except DecodeError (Nat × List Char)
  | [], _, _, _ => .error .truncated
  | c :: rest, i, w, k =>
    match charToDigit? c with
    | none => .error .invalidDigit
    | some digit =>
      let i := i + digit * w
      let t := threshold k bias
      if digit < t then .ok (i, rest)
      else decodeInteger bias rest i (w * (base - t)) (k + base)

/-- Decodes the extension by inserting one code point per decoded integer; `fuel` bounds the iterations. -/
def decodeLoop (fuel : Nat) (chars : List Char) (n i bias : Nat) (output : List Nat) :
    Except DecodeError (List Nat) :=
  match chars with
  | [] => .ok output
  | _ =>
    match fuel with
    | 0 => .error .truncated
    | fuel + 1 => do
      let (i', rest) ← decodeInteger bias chars i 1 base
      let size := output.length + 1
      let n := n + i' / size
      if Nat.isValidChar n then
        decodeLoop fuel rest n (i' % size + 1) (adapt (i' - i) size (i == 0))
          (insertAt output (i' % size) n)
      else
        .error .invalidCodePoint

/-- Decodes Punycode text (RFC 3492). The function is total and reports malformed input as a `DecodeError`. -/
def decode (input : String) : Except DecodeError String := do
  let (reversedExtended, rest) := input.toList.reverse.span (· != delimiter)
  let basic := match rest with
    | [] => []
    | _ :: reversedBasic => reversedBasic.reverse
  if basic.any (·.toNat ≥ 128) then throw .nonBasicCodePoint
  let extended := reversedExtended.reverse
  let output ← decodeLoop extended.length extended initialN 0 initialBias (basic.map Char.toNat)
  return String.ofList (output.map Char.ofNat)

end Urllib.Punycode
