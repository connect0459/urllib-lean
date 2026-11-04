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

structure EncoderState where
  n : Nat
  delta : Nat
  bias : Nat
  handled : Nat
  output : List Char

def encodeCodePoint (basicCount : Nat) (st : EncoderState) (c : Nat) : EncoderState :=
  if c < st.n then
    { st with delta := st.delta + 1 }
  else if c = st.n then
    { st with
      delta := 0
      bias := adapt st.delta (st.handled + 1) (st.handled == basicCount)
      handled := st.handled + 1
      output := st.output ++ encodeIntegerFrom st.bias base st.delta }
  else
    st

def encodeStep (basicCount : Nat) (codePoints : List Nat) (st : EncoderState) : EncoderState :=
  let m := (codePoints.filter (· ≥ st.n)).foldl min 0x110000
  let st := { st with delta := st.delta + (m - st.n) * (st.handled + 1), n := m }
  let st := codePoints.foldl (encodeCodePoint basicCount) st
  { st with delta := st.delta + 1, n := st.n + 1 }

def encodeLoop (basicCount : Nat) (codePoints : List Nat) : Nat → EncoderState → EncoderState
  | 0, st => st
  | fuel + 1, st =>
    if st.handled < codePoints.length then
      encodeLoop basicCount codePoints fuel (encodeStep basicCount codePoints st)
    else
      st

def encode (input : String) : String :=
  let codePoints := input.toList.map Char.toNat
  let basic := input.toList.filter (·.toNat < 128)
  let basicPrefix := if basic.isEmpty then [] else basic ++ [delimiter]
  let initial : EncoderState :=
    { n := initialN, delta := 0, bias := initialBias, handled := basic.length, output := basicPrefix }
  String.ofList (encodeLoop basic.length codePoints (codePoints.length + 1) initial).output

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

def insertAt {α : Type} (xs : List α) (i : Nat) (x : α) : List α :=
  xs.take i ++ x :: xs.drop i

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
