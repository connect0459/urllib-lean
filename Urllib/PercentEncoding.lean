namespace Urllib.PercentEncoding

inductive EncodeSet where
  | c0Control
  | fragment
  | query
  | specialQuery
  | path
  | userinfo
  | component
  deriving Repr, DecidableEq

def inC0ControlSet (c : Char) : Bool :=
  c.toNat ≤ 0x1F || c.toNat > 0x7E

def inFragmentSet (c : Char) : Bool :=
  inC0ControlSet c || [' ', '"', '<', '>', '`'].contains c

def inQuerySet (c : Char) : Bool :=
  inC0ControlSet c || [' ', '"', '#', '<', '>'].contains c

def inSpecialQuerySet (c : Char) : Bool :=
  inQuerySet c || c == '\''

def inPathSet (c : Char) : Bool :=
  inQuerySet c || ['?', '^', '`', '{', '}'].contains c

def inUserinfoSet (c : Char) : Bool :=
  inPathSet c || ['/', ':', ';', '=', '@', '[', '\\', ']', '|'].contains c

def inComponentSet (c : Char) : Bool :=
  inUserinfoSet c || ('$'.toNat ≤ c.toNat && c.toNat ≤ '&'.toNat) || c == '+' || c == ','

def EncodeSet.contains : EncodeSet → Char → Bool
  | .c0Control => inC0ControlSet
  | .fragment => inFragmentSet
  | .query => inQuerySet
  | .specialQuery => inSpecialQuerySet
  | .path => inPathSet
  | .userinfo => inUserinfoSet
  | .component => inComponentSet

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n) else Char.ofNat (0x41 + n - 10)

def percentEncodeByte (b : UInt8) : String :=
  String.ofList ['%', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

def utf8PercentEncodeCodePoint (set : EncodeSet) (c : Char) : String :=
  if set.contains c then
    String.join ((String.singleton c).toUTF8.toList.map percentEncodeByte)
  else
    String.singleton c

def utf8PercentEncode (set : EncodeSet) (input : String) : String :=
  input.foldl (fun acc c => acc ++ utf8PercentEncodeCodePoint set c) ""

def hexValue? (b : UInt8) : Option Nat :=
  if 0x30 ≤ b.toNat ∧ b.toNat ≤ 0x39 then some (b.toNat - 0x30)
  else if 0x41 ≤ b.toNat ∧ b.toNat ≤ 0x46 then some (b.toNat - 0x41 + 10)
  else if 0x61 ≤ b.toNat ∧ b.toNat ≤ 0x66 then some (b.toNat - 0x61 + 10)
  else none

def decodeBytes : List UInt8 → List UInt8
  | [] => []
  | 0x25 :: h1 :: h2 :: rest =>
    match hexValue? h1, hexValue? h2 with
    | some hi, some lo => UInt8.ofNat (hi * 16 + lo) :: decodeBytes rest
    | _, _ => 0x25 :: decodeBytes (h1 :: h2 :: rest)
  | b :: rest => b :: decodeBytes rest
termination_by bytes => bytes.length

def percentDecode (bytes : ByteArray) : ByteArray :=
  ByteArray.mk (decodeBytes bytes.toList).toArray

def percentDecodeString (input : String) : ByteArray :=
  percentDecode input.toUTF8

structure Utf8State where
  codePoint : Nat := 0
  needed : Nat := 0
  seen : Nat := 0
  lower : Nat := 0x80
  upper : Nat := 0xBF

def replacementChar : Char := Char.ofNat 0xFFFD

def feedLead (n : Nat) (acc : List Char) : Utf8State × List Char :=
  if n ≤ 0x7F then
    ({}, Char.ofNat n :: acc)
  else if 0xC2 ≤ n ∧ n ≤ 0xDF then
    ({ needed := 1, codePoint := n &&& 0x1F }, acc)
  else if 0xE0 ≤ n ∧ n ≤ 0xEF then
    ({ needed := 2, codePoint := n &&& 0xF
       lower := if n = 0xE0 then 0xA0 else 0x80
       upper := if n = 0xED then 0x9F else 0xBF }, acc)
  else if 0xF0 ≤ n ∧ n ≤ 0xF4 then
    ({ needed := 3, codePoint := n &&& 0x7
       lower := if n = 0xF0 then 0x90 else 0x80
       upper := if n = 0xF4 then 0x8F else 0xBF }, acc)
  else
    ({}, replacementChar :: acc)

def feed (st : Utf8State) (n : Nat) (acc : List Char) : Utf8State × List Char :=
  if st.needed = 0 then
    feedLead n acc
  else if st.lower ≤ n ∧ n ≤ st.upper then
    let codePoint := (st.codePoint <<< 6) ||| (n &&& 0x3F)
    let seen := st.seen + 1
    if seen = st.needed then
      ({}, Char.ofNat codePoint :: acc)
    else
      ({ st with codePoint, seen, lower := 0x80, upper := 0xBF }, acc)
  else
    feedLead n (replacementChar :: acc)

def decodeUtf8Loop : Utf8State → List UInt8 → List Char → List Char
  | st, [], acc => if st.needed = 0 then acc else replacementChar :: acc
  | st, b :: rest, acc =>
    let (st', acc') := feed st b.toNat acc
    decodeUtf8Loop st' rest acc'

def utf8DecodeWithoutBom (bytes : ByteArray) : String :=
  let withoutBom :=
    match bytes.toList with
    | 0xEF :: 0xBB :: 0xBF :: rest => rest
    | all => all
  String.ofList (decodeUtf8Loop {} withoutBom []).reverse

end Urllib.PercentEncoding
