import Urllib.Unicode.Properties

namespace Urllib.Unicode

/-- Decodes hexadecimal code points; the list must not be empty. -/
def decodeCodePoints (fields : List String) : Option (List Char) :=
  if fields.isEmpty then none else fields.mapM fun field => (parseHex field).map Char.ofNat

/-- Parses a line `code point` followed by its decomposition into a one-code-point range. -/
def parseDecompositionLine (line : String) : Option (Range (List Char)) :=
  match line.splitOn " " with
  | cp :: rest => do
    let cp ← parseHex cp
    let value ← decodeCodePoints rest
    some { low := cp, high := cp, value }
  | [] => none

/-- Parses a line `first second composite`. -/
def parseCompositionLine (line : String) : Option ((Nat × Nat) × Char) :=
  match line.splitOn " " with
  | [first, second, composite] => do
    let first ← parseHex first
    let second ← parseHex second
    let composite ← parseHex composite
    some ((first, second), Char.ofNat composite)
  | _ => none

/-- The full canonical decompositions of non-Hangul characters, as ranges of one code point. -/
def decompositionTable : Array (Range (List Char)) :=
  (Data.canonicalDecompositions.splitOn "\n").filterMap parseDecompositionLine |>.toArray

/-- The primary composites keyed by the pair of code points that compose to them. -/
def compositionTable : Array ((Nat × Nat) × Char) :=
  (Data.compositionPairs.splitOn "\n").filterMap parseCompositionLine |>.toArray

/-- The first code point of the Hangul syllable block. -/
def hangulSBase : Nat := 0xAC00
/-- The first leading consonant jamo. -/
def hangulLBase : Nat := 0x1100
/-- The first vowel jamo. -/
def hangulVBase : Nat := 0x1161
/-- One before the first trailing consonant jamo. -/
def hangulTBase : Nat := 0x11A7
/-- The number of leading consonants. -/
def hangulLCount : Nat := 19
/-- The number of vowels. -/
def hangulVCount : Nat := 21
/-- The number of trailing consonants, counting the absent one. -/
def hangulTCount : Nat := 28
/-- The number of syllables sharing a leading consonant. -/
def hangulNCount : Nat := hangulVCount * hangulTCount
/-- The number of Hangul syllables. -/
def hangulSCount : Nat := hangulLCount * hangulNCount

/-- Whether `c` is a precomposed Hangul syllable. -/
def isHangulSyllable (c : Char) : Bool :=
  hangulSBase ≤ c.toNat && c.toNat < hangulSBase + hangulSCount

/-- The full canonical decomposition of `c`; the empty list means that `c` does not decompose. -/
def decomposition (c : Char) : List Char :=
  if c.toNat < 0xC0 then []
  else if isHangulSyllable c then
    let index := c.toNat - hangulSBase
    let lead := Char.ofNat (hangulLBase + index / hangulNCount)
    let vowel := Char.ofNat (hangulVBase + index % hangulNCount / hangulTCount)
    let trail := index % hangulTCount
    if trail == 0 then [lead, vowel] else [lead, vowel, Char.ofNat (hangulTBase + trail)]
  else (lookup? decompositionTable c.toNat).getD []

/-- The primary composite of the pair `first`, `second`, if there is one. -/
def compose (first second : Char) : Option Char :=
  if second.toNat < 0x300 then none
  else
    let leadIndex := first.toNat - hangulLBase
    let vowelIndex := second.toNat - hangulVBase
    if first.toNat ≥ hangulLBase && leadIndex < hangulLCount && second.toNat ≥ hangulVBase && vowelIndex < hangulVCount then
      some (Char.ofNat (hangulSBase + (leadIndex * hangulVCount + vowelIndex) * hangulTCount))
    else if isHangulSyllable first && (first.toNat - hangulSBase) % hangulTCount == 0 &&
        hangulTBase < second.toNat && second.toNat < hangulTBase + hangulTCount then
      some (Char.ofNat (first.toNat + (second.toNat - hangulTBase)))
    else
      (compositionTable.binSearch ((first.toNat, second.toNat), default)
        (fun a b => a.1.1 < b.1.1 || (a.1.1 == b.1.1 && a.1.2 < b.1.2))).map (·.2)

/-- Orders each maximal run of non-starters by combining class, keeping equal classes in their order. -/
def reorder (chars : List Char) : List Char :=
  go chars [] []
where
  flush (run : List Char) : List Char :=
    run.reverse.mergeSort fun a b => combiningClass a ≤ combiningClass b
  go : List Char → List Char → List Char → List Char
    | [], run, acc => acc ++ flush run
    | c :: rest, run, acc =>
      if combiningClass c == 0 then go rest [] (acc ++ flush run ++ [c])
      else go rest (c :: run) acc

/-- The state of canonical composition: the output so far, the last starter with its position, and the class of the last kept character. -/
structure ComposeState where
  /-- The output built so far. -/
  output : Array Char
  /-- The index in `output` of the last starter and the starter itself, if any. -/
  starter : Option (Nat × Char)
  /-- The combining class of the last character appended after the starter. -/
  lastClass : Nat

/-- One step of canonical composition. -/
def composeStep (state : ComposeState) (c : Char) : ComposeState :=
  let cc := combiningClass c
  match state.starter with
  | some (index, starter) =>
    match compose starter c with
    | some composed =>
      if state.lastClass < cc || state.lastClass == 0 then
        { state with output := state.output.set! index composed, starter := some (index, composed) }
      else
        { state with output := state.output.push c, lastClass := cc }
    | none => appendChar state c cc
  | none => appendChar state c cc
where
  appendChar (state : ComposeState) (c : Char) (cc : Nat) : ComposeState :=
    if cc == 0 then
      { output := state.output.push c, starter := some (state.output.size, c), lastClass := 0 }
    else
      { state with output := state.output.push c, lastClass := cc }

/-- Canonical composition of a canonically ordered, fully decomposed string. -/
def composeAll (chars : List Char) : List Char :=
  (chars.foldl composeStep { output := #[], starter := none, lastClass := 0 }).output.toList

/-- The canonical decomposition of `c`, or `c` itself when it does not decompose. -/
def decomposeChar (c : Char) : List Char :=
  match decomposition c with
  | [] => [c]
  | parts => parts

/-- Normalization Form C. -/
def nfc (chars : List Char) : List Char :=
  composeAll (reorder (chars.flatMap decomposeChar))

end Urllib.Unicode
