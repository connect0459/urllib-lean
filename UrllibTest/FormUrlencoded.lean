import UrllibTest.Support
import Urllib.FormUrlencoded

namespace UrllibTest.FormUrlencoded

open Urllib.FormUrlencoded

structure ParseCase where
  name : String
  input : String
  expected : List (String × String)

def bom : String := String.singleton (Char.ofNat 0xFEFF)

def replacement : String := String.singleton (Char.ofNat 0xFFFD)

def parseCases : List ParseCase := [
  { name := "parses a name without a value", input := "test", expected := [("test", "")] },
  { name := "keeps a literal byte order mark in the name and the value", input := bom ++ "test=" ++ bom, expected := [(bom ++ "test", bom)] },
  { name := "keeps a percent-encoded byte order mark in the name and the value", input := "%EF%BB%BFtest=%EF%BB%BF", expected := [(bom ++ "test", bom)] },
  { name := "decodes a percent-encoded noncharacter", input := "%EF%BF%BF=%EF%BF%BF", expected := [(String.singleton (Char.ofNat 0xFFFF), String.singleton (Char.ofNat 0xFFFF))] },
  { name := "replaces each invalid byte FE FF", input := "%FE%FF", expected := [(replacement ++ replacement, "")] },
  { name := "replaces each invalid byte FF FE", input := "%FF%FE", expected := [(replacement ++ replacement, "")] },
  { name := "keeps a non-ASCII literal as a name", input := "†&†=x", expected := [("†", ""), ("†", "x")] },
  { name := "replaces an incomplete percent-encoded sequence", input := "%C2", expected := [(replacement, "")] },
  { name := "keeps the text after an incomplete percent-encoded sequence", input := "%C2x", expected := [(replacement ++ "x", "")] },
  { name := "treats a charset parameter as an ordinary pair", input := "_charset_=windows-1252&test=%C2x", expected := [("_charset_", "windows-1252"), ("test", replacement ++ "x")] },
  { name := "parses the empty input as no pairs", input := "", expected := [] },
  { name := "parses a single letter as a name", input := "a", expected := [("a", "")] },
  { name := "parses a name and a value", input := "a=b", expected := [("a", "b")] },
  { name := "parses an empty value", input := "a=", expected := [("a", "")] },
  { name := "parses an empty name", input := "=b", expected := [("", "b")] },
  { name := "skips a lone ampersand", input := "&", expected := [] },
  { name := "skips a leading ampersand", input := "&a", expected := [("a", "")] },
  { name := "skips a trailing ampersand", input := "a&", expected := [("a", "")] },
  { name := "keeps repeated names", input := "a&a", expected := [("a", ""), ("a", "")] },
  { name := "parses several names without values", input := "a&b&c", expected := [("a", ""), ("b", ""), ("c", "")] },
  { name := "parses several pairs", input := "a=b&c=d", expected := [("a", "b"), ("c", "d")] },
  { name := "skips a trailing ampersand after pairs", input := "a=b&c=d&", expected := [("a", "b"), ("c", "d")] },
  { name := "skips runs of ampersands", input := "&&&a=b&&&&c=d&", expected := [("a", "b"), ("c", "d")] },
  { name := "keeps pairs that share a name in order", input := "a=a&a=b&a=c", expected := [("a", "a"), ("a", "b"), ("a", "c")] },
  { name := "splits at the first equals sign only", input := "a==a", expected := [("a", "=a")] },
  { name := "decodes plus as space", input := "a=a+b+c+d", expected := [("a", "a b c d")] },
  { name := "keeps a lone percent sign in a name", input := "%=a", expected := [("%", "a")] },
  { name := "keeps an escape with one hexadecimal digit in a name", input := "%a=a", expected := [("%a", "a")] },
  { name := "keeps an escape with a non-hexadecimal second digit", input := "%a_=a", expected := [("%a_", "a")] },
  { name := "decodes a percent-encoded name", input := "%61=a", expected := [("a", "a")] },
  { name := "decodes escapes of either letter case and plus in a name", input := "%61+%4d%4D=", expected := [("a MM", "")] },
  { name := "keeps a trailing percent sign in a value", input := "id=0&value=%", expected := [("id", "0"), ("value", "%")] },
  { name := "keeps an invalid escape before a valid one", input := "b=%2sf%2a", expected := [("b", "%2sf*")] },
  { name := "keeps a truncated escape before a valid one", input := "b=%2%2af%2a", expected := [("b", "%2*f*")] },
  { name := "keeps a percent sign before a valid escape", input := "b=%%2a", expected := [("b", "%*")] },
  { name := "decodes an escaped plus as plus", input := "a=%2B", expected := [("a", "+")] },
  { name := "decodes an escaped ampersand and equals sign inside a value", input := "a=%26%3D", expected := [("a", "&=")] }
]

def parseFailures : List String :=
  parseCases.filterMap fun c => if parse c.input == c.expected then none else some c.name

/-- info: [] -/
#guard_msgs in
#eval parseFailures

structure SerializeCase where
  name : String
  input : List (String × String)
  expected : String

def serializeCases : List SerializeCase := [
  { name := "serializes no pairs as the empty string", input := [], expected := "" },
  { name := "serializes one pair", input := [("a", "b")], expected := "a=b" },
  { name := "joins pairs with ampersands", input := [("a", "b"), ("c", "d")], expected := "a=b&c=d" },
  { name := "serializes an empty value", input := [("a", "")], expected := "a=" },
  { name := "serializes an empty name", input := [("", "b")], expected := "=b" },
  { name := "serializes an empty pair", input := [("", "")], expected := "=" },
  { name := "keeps repeated names in order", input := [("a", "1"), ("a", "2")], expected := "a=1&a=2" },
  { name := "serializes a space as plus", input := [("a b", "c d")], expected := "a+b=c+d" },
  { name := "encodes a plus sign", input := [("a+b", "c+d")], expected := "a%2Bb=c%2Bd" },
  { name := "encodes ampersand and equals sign", input := [("a&b", "c=d")], expected := "a%26b=c%3Dd" },
  { name := "encodes a percent sign", input := [("%", "%41")], expected := "%25=%2541" },
  { name := "encodes the characters that URI component encoders leave alone", input := [("!'()~", "x")], expected := "%21%27%28%29%7E=x" },
  { name := "keeps asterisk, hyphen, dot and underscore", input := [("*-._", "azAZ09")], expected := "*-._=azAZ09" },
  { name := "encodes a non-ASCII code point as UTF-8", input := [("é", "あ")], expected := "%C3%A9=%E3%81%82" },
  { name := "encodes a supplementary-plane code point as four bytes", input := [("a", String.singleton (Char.ofNat 0x1F600))], expected := "a=%F0%9F%98%80" },
  { name := "encodes a byte order mark", input := [(bom, "")], expected := "%EF%BB%BF=" },
  { name := "encodes a control character", input := [("a", "\n")], expected := "a=%0A" }
]

def serializeFailures : List String :=
  serializeCases.filterMap fun c => if serialize c.input == c.expected then none else some c.name

/-- info: [] -/
#guard_msgs in
#eval serializeFailures

def roundTripInputs : List (List (String × String)) := [
  [],
  [("a", "b")],
  [("", "")],
  [("a b", "c+d"), ("e&f", "g=h")],
  [("%41", "100%"), ("~!*'()", "x y")],
  [("é", "あ"), ("a", String.singleton (Char.ofNat 0x1F600))],
  [(bom, bom), ("a", "a"), ("a", "b")]
]

def guardChecks : List UrllibTest.Check := [
  { name := "parses the bytes of the input like the string parser", holds := parseCases.all fun c => parseBytes c.input.toUTF8 == parse c.input },
  { name := "parses raw bytes that are not valid UTF-8 with replacement", holds := parseBytes (ByteArray.mk #[0x61, 0x3D, 0xFF]) == [("a", replacement)] },
  { name := "parses a plus byte as a space", holds := parseBytes (ByteArray.mk #[0x2B]) == [(" ", "")] },
  { name := "parsing a serialization restores the pairs", holds := roundTripInputs.all fun pairs => parse (serialize pairs) == pairs },
  { name := "serializing a parse of a serialization changes nothing", holds := roundTripInputs.all fun pairs => serialize (parse (serialize pairs)) == serialize pairs },
  { name := "serialized output contains no space", holds := roundTripInputs.all fun pairs => !(serialize pairs).toList.contains ' ' }
]

/-- info: [] -/
#guard_msgs in
#eval UrllibTest.failedChecks guardChecks

end UrllibTest.FormUrlencoded
