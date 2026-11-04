namespace Urllib.Punycode

inductive DecodeError where
  | nonBasicCodePoint
  | invalidDigit
  | truncated
  | invalidCodePoint
  deriving Repr, DecidableEq

def base : Nat := 36
def tMin : Nat := 1
def tMax : Nat := 26
def skew : Nat := 38
def damp : Nat := 700
def initialBias : Nat := 72
def initialN : Nat := 128
def delimiter : Char := '-'

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

def adaptLoop (delta k : Nat) : Nat :=
  if delta > ((base - tMin) * tMax) / 2 then
    adaptLoop (delta / (base - tMin)) (k + base)
  else
    k + (base - tMin + 1) * delta / (delta + skew)
termination_by delta
decreasing_by
  unfold base tMin tMax at *
  omega

def adapt (delta numPoints : Nat) (firstTime : Bool) : Nat :=
  let delta := if firstTime then delta / damp else delta / 2
  adaptLoop (delta + delta / numPoints) 0

def digitToChar (d : Nat) : Char :=
  if d < 26 then Char.ofNat (97 + d) else Char.ofNat (22 + d)

def charToDigit? (c : Char) : Option Nat :=
  if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat - 65)
  else if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat - 97)
  else if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48 + 26)
  else none

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

def insertAt {α : Type} (xs : List α) (i : Nat) (x : α) : List α :=
  xs.take i ++ x :: xs.drop i

def insertionPosition (current : List (Nat × Nat)) (item : Nat × Nat) : Nat :=
  (current.filter (fun x => decide (x.2 < item.2))).length

def itemLe (a b : Nat × Nat) : Bool :=
  decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2))

def encodeInsertions : List (Nat × Nat) → Nat → Nat → Nat → List (Nat × Nat) → List Char
  | _, _, _, _, [] => []
  | current, n, i, bias, item :: rest =>
    let size := current.length + 1
    let position := insertionPosition current item
    let delta := (item.1 - n) * size + position - i
    encodeIntegerFrom bias base delta ++
      encodeInsertions (insertAt current position item) item.1 (position + 1)
        (adapt delta size (i == 0)) rest

def basicItems (codePoints : List Nat) : List (Nat × Nat) :=
  codePoints.zipIdx.filter (fun x => decide (x.1 < 128))

def planOf (codePoints : List Nat) : List (Nat × Nat) :=
  (codePoints.zipIdx.filter (fun x => decide (128 ≤ x.1))).mergeSort (fun a b => itemLe a b)

def encode (input : String) : String :=
  let codePoints := input.toList.map Char.toNat
  let basic := basicItems codePoints
  let basicPrefix :=
    if basic.isEmpty then [] else basic.map (fun x => Char.ofNat x.1) ++ [delimiter]
  String.ofList (basicPrefix ++ encodeInsertions basic initialN 0 initialBias (planOf codePoints))

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
