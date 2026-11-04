import Urllib.PercentEncoding

namespace Urllib.FormUrlencoded

/-- The name-value pairs of an `application/x-www-form-urlencoded` payload. -/
abbrev Pairs := List (String × String)

/-- Replaces each plus sign byte by a space byte. -/
def plusToSpace (bytes : List UInt8) : List UInt8 :=
  bytes.map fun b => if b == 0x2B then 0x20 else b

/-- Decodes one name or value: plus becomes space, then percent-decoding and UTF-8 decoding without BOM handling. -/
def decodeComponent (bytes : List UInt8) : String :=
  PercentEncoding.utf8DecodeWithoutBom
    (PercentEncoding.percentDecode (ByteArray.mk (plusToSpace bytes).toArray))

/-- Splits a non-empty sequence at its first equals sign; without one, the whole sequence is the name and the value is empty. -/
def parseSequence (sequence : List UInt8) : String × String :=
  let (name, rest) := sequence.span fun b => b != 0x3D
  (decodeComponent name, decodeComponent (rest.drop 1))

/-- Parses an `application/x-www-form-urlencoded` byte sequence into pairs; empty sequences between ampersands are skipped. -/
def parseBytes (input : ByteArray) : Pairs :=
  (input.data.toList.splitOn 0x26).filter (fun sequence => !sequence.isEmpty) |>.map parseSequence

/-- Parses an `application/x-www-form-urlencoded` string, taking its UTF-8 bytes. -/
def parse (input : String) : Pairs :=
  parseBytes input.toUTF8

/-- Serializes a name or a value: a space becomes a plus sign and every other member of the form-urlencoded set becomes UTF-8 percent escapes. -/
def serializeComponent (text : String) : String :=
  String.ofList (text.toList.flatMap fun c =>
    if c == ' ' then ['+'] else PercentEncoding.utf8PercentEncodeCodePointChars .formUrlencoded c)

/-- Serializes pairs as `name=value` joined by ampersands. -/
def serialize (pairs : Pairs) : String :=
  "&".intercalate (pairs.map fun (name, value) => serializeComponent name ++ "=" ++ serializeComponent value)

end Urllib.FormUrlencoded
