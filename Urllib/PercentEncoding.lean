namespace Urllib.PercentEncoding

/-- The percent-encode sets of the URL Standard. -/
inductive EncodeSet where
  /-- The C0 control percent-encode set. -/
  | c0Control
  /-- The fragment percent-encode set. -/
  | fragment
  /-- The query percent-encode set. -/
  | query
  /-- The special-query percent-encode set. -/
  | specialQuery
  /-- The path percent-encode set. -/
  | path
  /-- The userinfo percent-encode set. -/
  | userinfo
  /-- The component percent-encode set. -/
  | component
  deriving Repr, DecidableEq

/-- Membership in the C0 control percent-encode set: C0 controls and code points above `~`. -/
def inC0ControlSet (c : Char) : Bool :=
  c.toNat ≤ 0x1F || c.toNat > 0x7E

/-- Membership in the fragment percent-encode set. -/
def inFragmentSet (c : Char) : Bool :=
  inC0ControlSet c || [' ', '"', '<', '>', '`'].contains c

/-- Membership in the query percent-encode set. -/
def inQuerySet (c : Char) : Bool :=
  inC0ControlSet c || [' ', '"', '#', '<', '>'].contains c

/-- Membership in the special-query percent-encode set. -/
def inSpecialQuerySet (c : Char) : Bool :=
  inQuerySet c || c == '\''

/-- Membership in the path percent-encode set. -/
def inPathSet (c : Char) : Bool :=
  inQuerySet c || ['?', '^', '`', '{', '}'].contains c

/-- Membership in the userinfo percent-encode set. -/
def inUserinfoSet (c : Char) : Bool :=
  inPathSet c || ['/', ':', ';', '=', '@', '[', '\\', ']', '|'].contains c

/-- Membership in the component percent-encode set. -/
def inComponentSet (c : Char) : Bool :=
  inUserinfoSet c || ('$'.toNat ≤ c.toNat && c.toNat ≤ '&'.toNat) || c == '+' || c == ','

/-- Membership of a code point in the given percent-encode set. -/
def EncodeSet.contains : EncodeSet → Char → Bool
  | .c0Control => inC0ControlSet
  | .fragment => inFragmentSet
  | .query => inQuerySet
  | .specialQuery => inSpecialQuerySet
  | .path => inPathSet
  | .userinfo => inUserinfoSet
  | .component => inComponentSet

/-- The uppercase hexadecimal digit for `n`, which must be below 16. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n) else Char.ofNat (0x41 + n - 10)

/-- The characters of the percent-encoding of a byte: `%` and two uppercase hexadecimal digits. -/
def percentEncodeByteChars (b : UInt8) : List Char :=
  ['%', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

/-- Percent-encodes a byte. -/
def percentEncodeByte (b : UInt8) : String :=
  String.ofList (percentEncodeByteChars b)

/-- The characters of the UTF-8 percent-encoding of a code point: the code point itself when outside the set, otherwise the escapes of its UTF-8 bytes. -/
def utf8PercentEncodeCodePointChars (set : EncodeSet) (c : Char) : List Char :=
  if set.contains c then
    (String.singleton c).toUTF8.data.toList.flatMap percentEncodeByteChars
  else
    [c]

/-- UTF-8 percent-encodes a code point with respect to a set. -/
def utf8PercentEncodeCodePoint (set : EncodeSet) (c : Char) : String :=
  String.ofList (utf8PercentEncodeCodePointChars set c)

/-- UTF-8 percent-encodes every code point of a string with respect to a set. -/
def utf8PercentEncode (set : EncodeSet) (input : String) : String :=
  String.ofList (input.toList.flatMap (utf8PercentEncodeCodePointChars set))

/-- The value of an ASCII hexadecimal digit byte in either letter case; `none` for any other byte. -/
def hexValue? (b : UInt8) : Option Nat :=
  if 0x30 ≤ b.toNat ∧ b.toNat ≤ 0x39 then some (b.toNat - 0x30)
  else if 0x41 ≤ b.toNat ∧ b.toNat ≤ 0x46 then some (b.toNat - 0x41 + 10)
  else if 0x61 ≤ b.toNat ∧ b.toNat ≤ 0x66 then some (b.toNat - 0x61 + 10)
  else none

/-- Replaces each `%XX` escape by its byte; a `%` not followed by two hexadecimal digits is kept as is. -/
def decodeBytes : List UInt8 → List UInt8
  | [] => []
  | 0x25 :: h1 :: h2 :: rest =>
    match hexValue? h1, hexValue? h2 with
    | some hi, some lo => UInt8.ofNat (hi * 16 + lo) :: decodeBytes rest
    | _, _ => 0x25 :: decodeBytes (h1 :: h2 :: rest)
  | b :: rest => b :: decodeBytes rest
termination_by bytes => bytes.length

/-- Percent-decodes a byte sequence. -/
def percentDecode (bytes : ByteArray) : ByteArray :=
  ByteArray.mk (decodeBytes bytes.data.toList).toArray

/-- Percent-decodes the UTF-8 bytes of a string. -/
def percentDecodeString (input : String) : ByteArray :=
  percentDecode input.toUTF8

/-- The state of the UTF-8 decoder of the Encoding Standard. -/
structure Utf8State where
  /-- The code point accumulated from the bytes seen so far. -/
  codePoint : Nat := 0
  /-- The number of continuation bytes the current sequence requires. -/
  needed : Nat := 0
  /-- The number of continuation bytes consumed so far. -/
  seen : Nat := 0
  /-- The lowest value accepted for the next continuation byte. -/
  lower : Nat := 0x80
  /-- The highest value accepted for the next continuation byte. -/
  upper : Nat := 0xBF

/-- The replacement character U+FFFD. -/
def replacementChar : Char := Char.ofNat 0xFFFD

/-- Handles a byte in the lead position: an ASCII byte, the lead byte of a multi-byte sequence, or an invalid byte that emits U+FFFD. -/
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

/-- Consumes one byte; an unexpected byte emits U+FFFD and is reprocessed in the lead position. Characters accumulate in reverse. -/
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

/-- Runs the decoder over the bytes, accumulating characters in reverse; a truncated final sequence emits U+FFFD. -/
def decodeUtf8Loop : Utf8State → List UInt8 → List Char → List Char
  | st, [], acc => if st.needed = 0 then acc else replacementChar :: acc
  | st, b :: rest, acc =>
    let (st', acc') := feed st b.toNat acc
    decodeUtf8Loop st' rest acc'

/-- UTF-8 decodes the bytes, ignoring a leading byte order mark and replacing malformed sequences with U+FFFD. -/
def utf8DecodeWithoutBom (bytes : ByteArray) : String :=
  let withoutBom :=
    match bytes.data.toList with
    | 0xEF :: 0xBB :: 0xBF :: rest => rest
    | all => all
  String.ofList (decodeUtf8Loop {} withoutBom []).reverse

end Urllib.PercentEncoding
