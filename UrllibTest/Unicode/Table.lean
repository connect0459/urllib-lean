import UrllibTest.Support
import Urllib.Unicode.Table

namespace UrllibTest.Unicode.Table

open Urllib.Unicode

def sample : String := "10 1F V\n30 30 W\n41 5A V\n61 7A X"

def decodeLetter (fields : List String) : Option String :=
  match fields with
  | [letter] => some letter
  | _ => none

def table : Array (Range String) := parseTable decodeLetter sample

def checks : List UrllibTest.Check := [
  { name := "parses one range per well-formed line", holds := table.size == 4 },
  { name := "finds the first code point of the first range", holds := lookup? table 0x10 == some "V" },
  { name := "finds the last code point of a range", holds := lookup? table 0x1F == some "V" },
  { name := "finds a single-code-point range", holds := lookup? table 0x30 == some "W" },
  { name := "finds a code point inside the last range", holds := lookup? table 0x70 == some "X" },
  { name := "finds a code point inside a middle range", holds := lookup? table 0x4D == some "V" },
  { name := "does not find a code point below the first range", holds := lookup? table 0x0F == none },
  { name := "does not find a code point in a gap", holds := lookup? table 0x20 == none },
  { name := "does not find a code point above the last range", holds := lookup? table 0x7B == none },
  { name := "does not find anything in an empty table", holds := lookup? (#[] : Array (Range String)) 0x41 == none },
  { name := "skips a line whose payload does not decode", holds := (parseTable decodeLetter "10 1F V W\n20 2F V").size == 1 },
  { name := "skips a line with too few fields", holds := (parseTable decodeLetter "10\n\n20 2F V").size == 1 },
  { name := "skips a line with a non-hexadecimal bound", holds := (parseTable decodeLetter "1G 1F V\n20 2F V").size == 1 },
  { name := "skips a line with a non-hexadecimal upper bound", holds := (parseTable decodeLetter "10 ZZ V").isEmpty },
  { name := "parses an empty input as an empty table", holds := (parseTable decodeLetter "").isEmpty },
  { name := "reads upper and lower case hexadecimal digits", holds := parseHex "1f" == some 31 && parseHex "1F" == some 31 && parseHex "10FFFF" == some 0x10FFFF },
  { name := "rejects a non-hexadecimal digit", holds := parseHex "1g" == none },
  { name := "rejects the empty hexadecimal string", holds := parseHex "" == none },
  { name := "reads every hexadecimal digit at the edges of its class", holds := ['0', '9', 'A', 'F', 'a', 'f'].map hexDigitValue? == [some 0, some 9, some 10, some 15, some 10, some 15] },
  { name := "rejects the characters next to each class of hexadecimal digits", holds := ['/', ':', '@', 'G', '`', 'g'].all fun c => (hexDigitValue? c).isNone },
  { name := "decodes an empty payload as unit", holds := (decodeUnit []).isSome },
  { name := "rejects a non-empty payload as unit", holds := (decodeUnit ["x"]).isNone },
  { name := "decodes one decimal number", holds := decodeNat ["230"] == some 230 },
  { name := "rejects an empty payload as a number", holds := (decodeNat []).isNone },
  { name := "rejects a payload that is not a number", holds := (decodeNat ["x"]).isNone },
  { name := "rejects a payload of several words as a number", holds := (decodeNat ["1", "2"]).isNone },
  { name := "decodes one word", holds := decodeName ["AL"] == some "AL" },
  { name := "rejects an empty payload as a word", holds := (decodeName []).isNone },
  { name := "rejects a payload of several words as a word", holds := (decodeName ["A", "B"]).isNone }
]

/-- info: [] -/
#guard_msgs in
#eval UrllibTest.failedChecks checks

end UrllibTest.Unicode.Table
