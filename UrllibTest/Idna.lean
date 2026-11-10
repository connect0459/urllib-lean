import UrllibTest.Support
import UrllibTest.Idna.Vectors
import Urllib.Idna

namespace UrllibTest.Idna

open Urllib

structure Vector where
  source : String
  toUnicode : String
  toUnicodeStatus : List String
  toAscii : String
  toAsciiStatus : List String

def hexValue (digits : List Char) : Nat :=
  digits.foldl (fun acc c => acc * 16 + (if c.isDigit then c.toNat - 48 else c.toNat - (if c.isUpper then 55 else 87))) 0

def unescapeWith : Nat → List Char → List Char
  | 0, chars => chars
  | fuel + 1, '\\' :: 'u' :: a :: b :: c :: d :: rest => Char.ofNat (hexValue [a, b, c, d]) :: unescapeWith fuel rest
  | fuel + 1, '\\' :: 'x' :: '{' :: rest =>
    let digits := rest.takeWhile (· != '}')
    Char.ofNat (hexValue digits) :: unescapeWith fuel (rest.drop (digits.length + 1))
  | fuel + 1, c :: rest => c :: unescapeWith fuel rest
  | _ + 1, [] => []

def unescape (chars : List Char) : List Char := unescapeWith chars.length chars

def trim (text : String) : String :=
  String.ofList ((text.toList.dropWhile fun c => c == ' ' || c == '\t').reverse.dropWhile fun c => c == ' ' || c == '\t').reverse

def column (text : String) : String :=
  if text == "\"\"" then "" else String.ofList (unescape text.toList)

def statusCodes (text : String) : List String :=
  (text.replace "[" "" |>.replace "]" "" |>.splitOn ",").map trim |>.filter (!·.isEmpty)

def parseVector (line : String) : Option Vector :=
  match line.splitOn ";" with
  | [source, unicode, unicodeStatus, ascii, asciiStatus, _, _] =>
    let sourceText := column source
    let unicodeText := if unicode.isEmpty then sourceText else column unicode
    let unicodeCodes := statusCodes unicodeStatus
    let asciiText := if ascii.isEmpty then unicodeText else column ascii
    let asciiCodes := if asciiStatus.isEmpty then unicodeCodes else statusCodes asciiStatus
    some { source := sourceText, toUnicode := unicodeText, toUnicodeStatus := unicodeCodes, toAscii := asciiText, toAsciiStatus := asciiCodes }
  | _ => none

def allVectors : List Vector := (vectors.splitOn "\n").filterMap parseVector

def ignoredCodes (options : Idna.Options) (forAscii : Bool) : List String :=
  (if options.checkHyphens then [] else ["V2", "V3"]) ++
  (if options.useStd3AsciiRules then [] else ["U1"]) ++
  (if forAscii && options.verifyDnsLength then [] else ["A4_1", "A4_2"]) ++
  (if forAscii then [] else ["X4_2"]) ++
  (if options.checkBidi then [] else ["B1", "B2", "B3", "B4", "B5", "B6"]) ++
  (if options.checkJoiners then [] else ["C1", "C2"])

def hasError (options : Idna.Options) (forAscii : Bool) (codes : List String) : Bool :=
  codes.any fun code => !(ignoredCodes options forAscii).contains code

def unicodeFailures (options : Idna.Options) : List String :=
  allVectors.filterMap fun v =>
    let (value, errors) := Idna.toUnicode options v.source
    let expectedError := hasError options false v.toUnicodeStatus
    if expectedError != !errors.isEmpty then some s!"error mismatch: {repr v.source}"
    else if !expectedError && value != v.toUnicode then some s!"value mismatch: {repr v.source}"
    else none

def asciiFailures (options : Idna.Options) : List String :=
  allVectors.filterMap fun v =>
    let expectedError := hasError options true v.toAsciiStatus
    match Idna.toAscii options v.source with
    | .error _ => if expectedError then none else some s!"unexpected error: {repr v.source}"
    | .ok value =>
      if expectedError then some s!"missing error: {repr v.source}"
      else if value != v.toAscii then some s!"value mismatch: {repr v.source}"
      else none

/-- info: [] -/
#guard_msgs in
#eval (unicodeFailures (Idna.Options.whatwg false)).take 20

/-- info: [] -/
#guard_msgs in
#eval (asciiFailures (Idna.Options.whatwg false)).take 20

/-- info: [] -/
#guard_msgs in
#eval (unicodeFailures (Idna.Options.whatwg true)).take 20

/-- info: [] -/
#guard_msgs in
#eval (asciiFailures (Idna.Options.whatwg true)).take 20

def hyphenChecking : Idna.Options := { Idna.Options.whatwg true with checkHyphens := true }

def unchecked : Idna.Options :=
  { checkHyphens := false, checkBidi := false, checkJoiners := false, useStd3AsciiRules := false, verifyDnsLength := false }

/-- info: [] -/
#guard_msgs in
#eval (unicodeFailures hyphenChecking).take 20

/-- info: [] -/
#guard_msgs in
#eval (asciiFailures hyphenChecking).take 20

/-- info: [] -/
#guard_msgs in
#eval (unicodeFailures unchecked).take 20

/-- info: [] -/
#guard_msgs in
#eval (asciiFailures unchecked).take 20

def lenient : Idna.Options := Idna.Options.whatwg false

def strict : Idna.Options := Idna.Options.whatwg true

def asciiOf (options : Idna.Options) (domain : String) : Option String :=
  (Idna.toAscii options domain).toOption

def errorsOf (options : Idna.Options) (domain : String) : List Idna.Error :=
  match Idna.toAscii options domain with
  | .error errors => errors
  | .ok _ => []

def longLabel (n : Nat) : String := String.ofList (List.replicate n 'a')

def checks : List UrllibTest.Check := [
  { name := "the vector file is loaded", holds := allVectors.length + skippedLines > 6000 },
  { name := "the table agrees with the ASCII answers for every ASCII code point", holds := (List.range 128).all fun n => Idna.tableStatus (Char.ofNat n) == Idna.status (Char.ofNat n) },
  { name := "splitting the empty string yields one empty label", holds := Idna.splitDots [] == [[]] },
  { name := "splitting at a full stop yields the labels around it", holds := Idna.splitDots "a.bc".toList == ["a".toList, "bc".toList] },
  { name := "splitting keeps the empty label after a trailing full stop", holds := Idna.splitDots "a.".toList == ["a".toList, []] },
  { name := "splitting keeps the empty label before a leading full stop", holds := Idna.splitDots ".a".toList == [[], "a".toList] },
  { name := "splitting a string without a full stop yields it whole", holds := Idna.splitDots "abc".toList == ["abc".toList] },
  { name := "joining no labels yields the empty string", holds := Idna.joinDots [] == [] },
  { name := "joining one label yields it unchanged", holds := Idna.joinDots ["ab".toList] == "ab".toList },
  { name := "joining labels inserts full stops between them", holds := Idna.joinDots ["a".toList, [], "b".toList] == "a..b".toList },
  { name := "joining inverts splitting", holds := ["", "a", "a.b", ".", "a..b.", ".a"].all fun s => Idna.joinDots (Idna.splitDots s.toList) == s.toList },
  { name := "an ASCII label is not encoded", holds := Idna.encodeLabel "abc".toList == "abc".toList },
  { name := "a non-ASCII label is encoded with the ACE prefix", holds := Idna.encodeLabel "bücher".toList == "xn--bcher-kva".toList },
  { name := "converting a domain again does not change a successful result", holds := allVectors.all fun v => match Idna.toAscii lenient v.source with
      | .ok value => asciiOf lenient value == some value
      | .error _ => true },
  { name := "a status payload decodes valid", holds := Idna.decodeStatus ["V"] == some .valid },
  { name := "a status payload decodes disallowed", holds := Idna.decodeStatus ["X"] == some .disallowed },
  { name := "a status payload decodes ignored", holds := Idna.decodeStatus ["I"] == some .ignored },
  { name := "a status payload decodes a mapping", holds := Idna.decodeStatus ["M", "0061", "0062"] == some (.mapped ['a', 'b']) },
  { name := "a status payload decodes a deviation", holds := Idna.decodeStatus ["D", "0073", "0073"] == some (.deviation ['s', 's']) },
  { name := "a disallowed status with a payload is rejected", holds := (Idna.decodeStatus ["X", "0061"]).isNone },
  { name := "an ignored status with a payload is rejected", holds := (Idna.decodeStatus ["I", "0061"]).isNone },
  { name := "the validity criteria hold for the empty label", holds := Idna.validityErrors strict [] == [] },
  { name := "a left brace fails with the STD3 rules", holds := errorsOf strict "a{b.com" == [.std3AsciiRule] },
  { name := "an exclamation mark fails with the STD3 rules", holds := errorsOf strict "a!b.com" == [.std3AsciiRule] },
  { name := "digits and hyphens pass with the STD3 rules", holds := (asciiOf strict "a-0-9z.com").isSome },
  { name := "a zero width non-joiner at the start of a label is rejected", holds := (errorsOf lenient "\u200C\u0628").contains .contextJ },
  { name := "a zero width non-joiner at the end of a label is rejected", holds := (errorsOf lenient "\u0628\u200C").contains .contextJ },
  { name := "a zero width non-joiner after a joining letter and before a non-joining letter is rejected", holds := (errorsOf lenient "\u0628\u200Ca").contains .contextJ },
  { name := "a zero width non-joiner between joining letters with transparent marks around it is accepted", holds := (asciiOf lenient "\u0628\u064B\u200C\u064B\u0628").isSome },
  { name := "a zero width non-joiner between a dual-joining and a right-joining letter is accepted", holds := (asciiOf lenient "\u0628\u200C\u0627").isSome },
  { name := "a zero width non-joiner after a left-joining letter is accepted", holds := (asciiOf { lenient with checkBidi := false } "\uA872\u200C\u0627").isSome },
  { name := "a status payload with an unknown letter is rejected", holds := (Idna.decodeStatus ["Q"]).isNone },
  { name := "an empty status payload is rejected", holds := (Idna.decodeStatus []).isNone },
  { name := "a mapping with a bad target is rejected", holds := (Idna.decodeStatus ["M", "zz"]).isNone },
  { name := "a deviation with a bad target is rejected", holds := (Idna.decodeStatus ["D", "zz"]).isNone },
  { name := "a valid status with a payload is rejected", holds := (Idna.decodeStatus ["V", "0061"]).isNone },
  { name := "an uppercase ASCII letter maps to lowercase", holds := Idna.mapChar 'Q' == ['q'] },
  { name := "a soft hyphen is removed", holds := Idna.mapChar (Char.ofNat 0xAD) == [] },
  { name := "a deviation character is kept in nontransitional processing", holds := Idna.mapChar (Char.ofNat 0xDF) == [Char.ofNat 0xDF] },
  { name := "an ideographic full stop maps to a full stop", holds := Idna.mapChar (Char.ofNat 0x3002) == ['.'] },
  { name := "a code point that is not assigned is disallowed", holds := Idna.status (Char.ofNat 0x378) == .disallowed },
  { name := "an ASCII domain is lowercased", holds := asciiOf lenient "ExAmple.COM" == some "example.com" },
  { name := "a non-ASCII label is encoded as Punycode", holds := asciiOf lenient "bücher.de" == some "xn--bcher-kva.de" },
  { name := "a Punycode label is decoded by toUnicode", holds := (Idna.toUnicode lenient "xn--bcher-kva.de").1 == "bücher.de" },
  { name := "an empty domain has no errors without the length check", holds := asciiOf lenient "" == some "" },
  { name := "an empty domain violates the length check", holds := errorsOf strict "" == [.labelLength, .domainLength] },
  { name := "a trailing root label is kept without the length check", holds := asciiOf lenient "example.com." == some "example.com." },
  { name := "a trailing root label violates the length check", holds := errorsOf strict "example.com." == [.labelLength] },
  { name := "a label of 63 characters passes the length check", holds := (asciiOf strict (longLabel 63 ++ ".com")).isSome },
  { name := "a label of 64 characters violates the length check", holds := errorsOf strict (longLabel 64 ++ ".com") == [.labelLength] },
  { name := "a domain of 253 characters passes the length check", holds := (asciiOf strict (String.intercalate "." [longLabel 63, longLabel 63, longLabel 63, longLabel 61])).isSome },
  { name := "a domain of 254 characters violates the length check", holds := errorsOf strict (String.intercalate "." [longLabel 63, longLabel 63, longLabel 63, longLabel 62]) == [.domainLength] },
  { name := "a long label is accepted when the length is not verified", holds := (asciiOf lenient (longLabel 64 ++ ".com")).isSome },
  { name := "an underscore passes without the STD3 rules", holds := asciiOf lenient "a_b.com" == some "a_b.com" },
  { name := "an underscore fails with the STD3 rules", holds := errorsOf strict "a_b.com" == [.std3AsciiRule] },
  { name := "a hyphen in the third and fourth positions is accepted without hyphen checking", holds := asciiOf lenient "ab--c.com" == some "ab--c.com" },
  { name := "a hyphen in the third and fourth positions is rejected with hyphen checking", holds := errorsOf hyphenChecking "ab--c.com" == [.hyphenInThirdAndFourthPosition] },
  { name := "a leading hyphen is rejected with hyphen checking", holds := errorsOf hyphenChecking "-a.com" == [.hyphenAtEdge] },
  { name := "a trailing hyphen is rejected with hyphen checking", holds := errorsOf hyphenChecking "a-.com" == [.hyphenAtEdge] },
  { name := "a Punycode label with an invalid digit is rejected", holds := errorsOf lenient "xn--a!.com" == [.invalidPunycode] },
  { name := "a Punycode label that decodes to a control character is rejected", holds := errorsOf lenient "xn--a.com" == [.invalidCodePoint] },
  { name := "a Punycode label that decodes to ASCII only is rejected", holds := errorsOf lenient "xn--a-.com" == [.emptyOrAsciiPunycodeLabel] },
  { name := "an empty Punycode label is rejected", holds := errorsOf lenient "xn--.com" == [.emptyOrAsciiPunycodeLabel] },
  { name := "a Punycode label with a non-ASCII code point is rejected", holds := errorsOf lenient "xn--é.com" == [.nonAsciiPunycodeLabel] },
  { name := "a label that starts with a combining mark is rejected", holds := errorsOf lenient (String.singleton (Char.ofNat 0x300) ++ "a.com") == [.startsWithMark] },
  { name := "a Punycode label that decodes to a non-normalized label is rejected", holds := errorsOf lenient "xn--a-vbb.com" == [.notNormalized] },
  { name := "a decoded label that starts with the ACE prefix is rejected", holds := errorsOf lenient "xn--xn---epa.com" == [.startsWithAcePrefix] },
  { name := "a label that contains a full stop is rejected", holds := Idna.validityErrors lenient ['a', '.'] == [.containsFullStop] },
  { name := "a zero width non-joiner after a virama is accepted", holds := (asciiOf lenient ("\u0915\u094D\u200C\u0937")).isSome },
  { name := "a zero width non-joiner between two letters is rejected", holds := errorsOf lenient ("a\u200Cb") == [.contextJ] },
  { name := "a zero width joiner after a virama is accepted", holds := (asciiOf lenient ("\u0915\u094D\u200D")).isSome },
  { name := "a zero width joiner without a virama is rejected", holds := (errorsOf lenient ("a\u200D")).contains .contextJ },
  { name := "a zero width non-joiner between joining letters is accepted", holds := (asciiOf lenient ("\u0628\u200C\u0628")).isSome },
  { name := "joiners are not checked when the check is off", holds := (asciiOf { lenient with checkJoiners := false } ("a\u200Cb")).isSome },
  { name := "a Hebrew label after a Latin label violates the Bidi rule", holds := (errorsOf lenient ("1a.\u05D0")).contains .bidi },
  { name := "a Hebrew label alone is accepted", holds := (asciiOf lenient "\u05D0\u05D1").isSome },
  { name := "the Bidi rule is not checked when the check is off", holds := (asciiOf { lenient with checkBidi := false } ("1a.\u05D0")).isSome },
  { name := "an Arabic label with European and Arabic digits is rejected", holds := (errorsOf lenient ("\u0627\u0661\u0031")).contains .bidi },
  { name := "the Bidi rule accepts the empty label", holds := Idna.bidiOk [] },
  { name := "the Bidi rule rejects a label that starts with a European number", holds := !Idna.bidiOk [.en, .l] },
  { name := "the Bidi rule accepts a left-to-right label ending in a European number", holds := Idna.bidiOk [.l, .en] },
  { name := "the Bidi rule accepts trailing nonspacing marks", holds := Idna.bidiOk [.r, .nsm, .nsm] },
  { name := "the Bidi rule rejects a right-to-left label ending in a separator", holds := !Idna.bidiOk [.r, .cs] },
  { name := "the Bidi rule rejects a left-to-right label ending in a separator", holds := !Idna.bidiOk [.l, .cs] },
  { name := "the Bidi rule rejects a left-to-right label with a right-to-left class", holds := !Idna.bidiOk [.l, .r] },
  { name := "toUnicode reports the errors and still converts", holds := (Idna.toUnicode lenient "A\u0300\u05D0.b").1 == "\u00E0\u05D0.b" }
]

/-- info: [] -/
#guard_msgs in
#eval UrllibTest.failedChecks checks

end UrllibTest.Idna
