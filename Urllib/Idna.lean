import Urllib.Punycode
import Urllib.Unicode.Normalization
import Urllib.Unicode.Data.IdnaMapping

namespace Urllib.Idna

open Urllib.Unicode

/-- The flags of UTS #46 processing; Transitional_Processing and IgnoreInvalidPunycode are fixed to false. -/
structure Options where
  /-- Reject labels with hyphens in the third and fourth positions or at either end. -/
  checkHyphens : Bool
  /-- Check the Bidi rule of RFC 5893 on every label of a Bidi domain name. -/
  checkBidi : Bool
  /-- Check the ContextJ rules for ZERO WIDTH NON-JOINER and ZERO WIDTH JOINER. -/
  checkJoiners : Bool
  /-- Allow only lowercase letters, digits, and the hyphen-minus among the ASCII code points. -/
  useStd3AsciiRules : Bool
  /-- Verify the DNS length limits in `toAscii`. -/
  verifyDnsLength : Bool
  deriving DecidableEq, Repr

/-- The flags the URL Standard passes to UTS #46 ToASCII; `beStrict` switches on STD3 rules and the length check. -/
def Options.whatwg (beStrict : Bool) : Options :=
  { checkHyphens := false, checkBidi := true, checkJoiners := true,
    useStd3AsciiRules := beStrict, verifyDnsLength := beStrict }

/-- A reason for UTS #46 to record an error. -/
inductive Error where
  /-- A label that starts with `xn--` contains a non-ASCII code point. -/
  | nonAsciiPunycodeLabel
  /-- The rest of a label that starts with `xn--` is not valid Punycode. -/
  | invalidPunycode
  /-- A label that starts with `xn--` decodes to nothing or to ASCII only. -/
  | emptyOrAsciiPunycodeLabel
  /-- A label is not in Normalization Form C. -/
  | notNormalized
  /-- A label has hyphens in the third and fourth positions. -/
  | hyphenInThirdAndFourthPosition
  /-- A label starts or ends with a hyphen. -/
  | hyphenAtEdge
  /-- A label starts with `xn--` after processing. -/
  | startsWithAcePrefix
  /-- A label contains a full stop. -/
  | containsFullStop
  /-- A label starts with a combining mark. -/
  | startsWithMark
  /-- A label contains a code point that is not valid. -/
  | invalidCodePoint
  /-- A label violates the STD3 ASCII rules. -/
  | std3AsciiRule
  /-- A label violates the ContextJ rules. -/
  | contextJ
  /-- A label violates the Bidi rule. -/
  | bidi
  /-- The domain is empty or longer than 253 code points. -/
  | domainLength
  /-- A label is empty or longer than 63 code points. -/
  | labelLength
  deriving DecidableEq, Repr

/-- The IDNA mapping status of a code point. -/
inductive Status where
  /-- Kept as is. -/
  | valid
  /-- Replaced by the target. -/
  | mapped (target : List Char)
  /-- Kept as is in nontransitional processing. -/
  | deviation (target : List Char)
  /-- Rejected by validation. -/
  | disallowed
  /-- Removed. -/
  | ignored
  deriving DecidableEq, Repr

/-- Decodes a mapping table payload: a status letter and the target code points. -/
def decodeStatus (fields : List String) : Option Status :=
  let targets (hex : List String) : Option (List Char) := hex.mapM fun h => (parseHex h).map Char.ofNat
  match fields with
  | ["V"] => some .valid
  | ["X"] => some .disallowed
  | ["I"] => some .ignored
  | "M" :: hex => (targets hex).map .mapped
  | "D" :: hex => (targets hex).map .deviation
  | _ => none

/-- The mapping table of the pinned Unicode version, parsed from the generated data. -/
def mappingTable : Array (Range Status) := parseTable decodeStatus Data.idnaMapping

/-- The status of a code point according to the mapping table alone. -/
def tableStatus (c : Char) : Status :=
  (lookup? mappingTable c.toNat).getD .disallowed

/-- The status of a code point; ASCII is answered directly, which agrees with the table. -/
def status (c : Char) : Status :=
  if c.toNat < 0x80 then
    if c.toNat < 0x41 || 0x5A < c.toNat then .valid else .mapped [Char.ofNat (c.toNat + 0x20)]
  else tableStatus c

/-- Step 1 of processing: the mapping of one code point. -/
def mapChar (c : Char) : List Char :=
  match status c with
  | .mapped target => target
  | .ignored => []
  | _ => [c]

/-- Whether a code point is ASCII. -/
def isAscii (c : Char) : Bool := c.toNat < 0x80

/-- The ASCII compatible encoding prefix. -/
def acePrefix : List Char := ['x', 'n', '-', '-']

/-- Whether the ContextJ rules hold for every ZERO WIDTH NON-JOINER and ZERO WIDTH JOINER of a label. -/
def contextJOk (label : List Char) : Bool :=
  go [] label
where
  go (before : List Char) : List Char → Bool
    | [] => true
    | c :: after =>
      let afterVirama := before.head?.any fun p => combiningClass p == 9
      let ok :=
        if c == Char.ofNat 0x200C then
          afterVirama ||
            ((before.dropWhile fun p => joiningType p == .transparent).head?.any
                (fun p => joiningType p == .leftJoining || joiningType p == .dualJoining) &&
              (after.dropWhile fun p => joiningType p == .transparent).head?.any
                (fun p => joiningType p == .rightJoining || joiningType p == .dualJoining))
        else if c == Char.ofNat 0x200D then afterVirama
        else true
      ok && go (c :: before) after

/-- The errors of the validity criteria of UTS #46 section 4.1 for a non-empty label, except for the Bidi rule. -/
def validityErrors (options : Options) (label : List Char) : List Error :=
  let hyphenErrors :=
    if options.checkHyphens then
      (if (label.drop 2).take 2 == ['-', '-'] then [Error.hyphenInThirdAndFourthPosition] else []) ++
      (if label.head? == some '-' || label.getLast? == some '-' then [Error.hyphenAtEdge] else [])
    else
      if label.take 4 == acePrefix then [Error.startsWithAcePrefix] else []
  let codePointErrors :=
    (if label.any fun c => match status c with | .valid | .deviation _ => false | _ => true then [Error.invalidCodePoint] else []) ++
    (if options.useStd3AsciiRules &&
        label.any fun c => isAscii c && !(('a' ≤ c ∧ c ≤ 'z') || ('0' ≤ c ∧ c ≤ '9') || c == '-') then
      [Error.std3AsciiRule] else [])
  (if nfc label == label then [] else [Error.notNormalized]) ++
  hyphenErrors ++
  (if label.contains '.' then [Error.containsFullStop] else []) ++
  (if label.head?.any isMark then [Error.startsWithMark] else []) ++
  codePointErrors ++
  (if options.checkJoiners && !contextJOk label then [Error.contextJ] else [])

/-- Whether a code point is right-to-left or an Arabic number; none is below U+0590. -/
def isRtl (c : Char) : Bool :=
  0x590 ≤ c.toNat && match bidiClass c with | .r | .al | .an => true | _ => false

/-- Whether a label contains a right-to-left or Arabic number code point. -/
def isRtlLabel (label : List Char) : Bool :=
  label.any isRtl

/-- The Bidi rule of RFC 5893 section 2 on the Bidi classes of a label. -/
def bidiOk (classes : List BidiClass) : Bool :=
  match classes with
  | [] => true
  | first :: _ =>
    let lastKept := (classes.reverse.dropWhile (· == .nsm)).head?
    match first with
    | .l =>
      classes.all (fun k => [BidiClass.l, .en, .es, .cs, .et, .on, .bn, .nsm].contains k) &&
        lastKept.any (fun k => k == .l || k == .en)
    | .r | .al =>
      classes.all (fun k => [BidiClass.r, .al, .an, .en, .es, .cs, .et, .on, .bn, .nsm].contains k) &&
        lastKept.any (fun k => k == .r || k == .al || k == .en || k == .an) &&
        !(classes.contains .en && classes.contains .an)
    | _ => false

/-- Converts a label that starts with `xn--` to Unicode; returns the label, the errors, and whether validation applies. -/
def convertLabel (label : List Char) : List Char × List Error × Bool :=
  if label.take 4 == acePrefix then
    if label.any fun c => !isAscii c then (label, [Error.nonAsciiPunycodeLabel], false)
    else
      match Punycode.decode (String.ofList (label.drop 4)) with
      | .error _ => (label, [Error.invalidPunycode], false)
      | .ok decoded =>
        let chars := decoded.toList
        (chars, if chars.isEmpty || chars.all isAscii then [Error.emptyOrAsciiPunycodeLabel] else [], true)
  else (label, [], true)

/-- Splits a code point list at every full stop; the result is never empty. -/
def splitDots (chars : List Char) : List (List Char) :=
  chars.foldr (fun c acc => if c == '.' then [] :: acc else (c :: acc.headD []) :: acc.tail) [[]]

/-- Joins labels with full stops. -/
def joinDots : List (List Char) → List Char
  | [] => []
  | [label] => label
  | label :: rest => label ++ '.' :: joinDots rest

/-- The labels that pass the Convert/Validate step together with the errors recorded for them. -/
def processConverted (options : Options) (converted : List (List Char × List Error × Bool)) :
    List (List Char) × List Error :=
  let isBidiDomain := options.checkBidi && converted.any fun (label, _, _) => isRtlLabel label
  let results := converted.map fun (label, errors, validate) =>
    (label,
      errors ++ (if validate && !label.isEmpty then validityErrors options label else []) ++
        (if isBidiDomain && !bidiOk (label.map bidiClass) then [Error.bidi] else []))
  (results.map (·.1), results.flatMap (·.2))

/-- Steps 3 and 4 of processing on the mapped and normalized string: the converted labels and the recorded errors. -/
def processMapped (options : Options) (mapped : List Char) : List (List Char) × List Error :=
  processConverted options ((splitDots mapped).map convertLabel)

/-- The processing steps of UTS #46 section 4: the converted labels and the recorded errors. -/
def processLabels (options : Options) (domain : List Char) : List (List Char) × List Error :=
  processMapped options (nfc (domain.flatMap mapChar))

/-- The processing steps of UTS #46 section 4: the converted domain and the recorded errors. -/
def process (options : Options) (domain : List Char) : List Char × List Error :=
  let (labels, errors) := processLabels options domain
  (joinDots labels, errors)

/-- Whether the DNS length restrictions of ToASCII are violated. -/
def lengthErrors (labels : List (List Char)) : List Error :=
  let trimmed := if labels.getLast? == some [] then labels.dropLast else labels
  let total := (trimmed.map List.length).sum + trimmed.length - 1
  (if labels.any (fun l => l.isEmpty || 63 < l.length) then [Error.labelLength] else []) ++
    (if total < 1 || 253 < total then [Error.domainLength] else [])

/-- ToASCII step 3: a label with non-ASCII code points becomes Punycode with the ACE prefix. -/
def encodeLabel (label : List Char) : List Char :=
  if label.all isAscii then label else acePrefix ++ (Punycode.encode (String.ofList label)).toList

/-- UTS #46 ToUnicode: the converted domain and the recorded errors. -/
def toUnicodeChars (options : Options) (domain : List Char) : List Char × List Error :=
  process options domain

/-- UTS #46 ToASCII on code points. -/
def toAsciiChars (options : Options) (domain : List Char) : Except (List Error) (List Char) :=
  let (labels, errors) := processLabels options domain
  let encoded := labels.map encodeLabel
  let allErrors := errors ++ (if options.verifyDnsLength then lengthErrors encoded else [])
  if allErrors.isEmpty then .ok (joinDots encoded) else .error allErrors

/-- UTS #46 ToUnicode. -/
def toUnicode (options : Options) (domain : String) : String × List Error :=
  let (chars, errors) := toUnicodeChars options domain.toList
  (String.ofList chars, errors)

/-- UTS #46 ToASCII. -/
def toAscii (options : Options) (domain : String) : Except (List Error) String :=
  (toAsciiChars options domain.toList).map String.ofList

end Urllib.Idna
