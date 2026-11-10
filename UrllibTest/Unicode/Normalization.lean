import UrllibTest.Support
import Urllib.Unicode.Normalization

namespace UrllibTest.Unicode.Normalization

open Urllib.Unicode

def cps (values : List Nat) : List Char := values.map Char.ofNat

structure Case where
  name : String
  input : List Nat
  expected : List Nat

def cases : List Case := [
  { name := "keeps an ASCII string", input := [0x61, 0x62], expected := [0x61, 0x62] },
  { name := "keeps the empty string", input := [], expected := [] },
  { name := "composes a base letter with a combining grave accent", input := [0x61, 0x300], expected := [0xE0] },
  { name := "composes a base letter with a combining acute accent", input := [0x41, 0x301], expected := [0xC1] },
  { name := "keeps a precomposed letter", input := [0xE0], expected := [0xE0] },
  { name := "composes in two steps through an intermediate composite", input := [0x61, 0x308, 0x304], expected := [0x1DF] },
  { name := "reorders combining marks by combining class", input := [0x61, 0x301, 0x323], expected := [0x1EA1, 0x301] },
  { name := "keeps combining marks of equal class in their order", input := [0x61, 0x301, 0x300], expected := [0xE1, 0x300] },
  { name := "does not compose across a blocking mark of the same class", input := [0x61, 0x300, 0x300], expected := [0xE0, 0x300] },
  { name := "does not compose a starter followed by a starter", input := [0x61, 0x62], expected := [0x61, 0x62] },
  { name := "composes a mark that follows a non-composing mark of lower class", input := [0x61, 0x323, 0x302], expected := [0x1EAD] },
  { name := "leaves a leading combining mark alone", input := [0x300, 0x61], expected := [0x300, 0x61] },
  { name := "leaves a leading combining mark alone even before a composing mark", input := [0x300, 0x301], expected := [0x300, 0x301] },
  { name := "replaces a singleton decomposition by its canonical equivalent", input := [0x212B], expected := [0xC5] },
  { name := "replaces the Ohm sign by the Greek capital omega", input := [0x2126], expected := [0x3A9] },
  { name := "does not recompose a composition-excluded character", input := [0x958], expected := [0x915, 0x93C] },
  { name := "does not recompose a character whose decomposition starts with a non-starter", input := [0x344], expected := [0x308, 0x301] },
  { name := "composes a Hangul leading and vowel jamo", input := [0x1100, 0x1161], expected := [0xAC00] },
  { name := "composes a Hangul syllable with a trailing consonant", input := [0xAC00, 0x11A8], expected := [0xAC01] },
  { name := "composes three Hangul jamo", input := [0x1100, 0x1161, 0x11A8], expected := [0xAC01] },
  { name := "decomposes and recomposes a Hangul syllable to itself", input := [0xAC01], expected := [0xAC01] },
  { name := "does not add a trailing consonant to a syllable that already has one", input := [0xAC01, 0x11A8], expected := [0xAC01, 0x11A8] },
  { name := "keeps a Hangul vowel jamo without a leading consonant", input := [0x1161], expected := [0x1161] },
  { name := "keeps a Hangul trailing consonant after a leading consonant", input := [0x1100, 0x11A8], expected := [0x1100, 0x11A8] },
  { name := "does not compose past a blocking mark of the same combining class", input := [0x61, 0x305, 0x301], expected := [0x61, 0x305, 0x301] },
  { name := "does not compose a leading Hangul consonant with a combining mark", input := [0x1100, 0x300], expected := [0x1100, 0x300] },
  { name := "composes a Japanese kana with a voiced sound mark", input := [0x304B, 0x3099], expected := [0x304C] },
  { name := "composes a supplementary-plane pair", input := [0x11099, 0x110BA], expected := [0x1109A] },
  { name := "keeps a supplementary-plane character without a decomposition", input := [0x1F600], expected := [0x1F600] },
  { name := "keeps a CJK ideograph", input := [0x4E00], expected := [0x4E00] },
  { name := "decomposes a character in the compatibility block into its canonical equivalent", input := [0xFA10], expected := [0x585A] },
  { name := "keeps a non-starter after an unrelated starter", input := [0x62, 0x300], expected := [0x62, 0x300] }
]

def failures : List String :=
  cases.filterMap fun c => if nfc (cps c.input) == cps c.expected then none else some c.name

/-- info: [] -/
#guard_msgs in
#eval failures

def checks : List UrllibTest.Check := [
  { name := "the combining class of an ASCII character is zero", holds := (List.range 128).all fun n => combiningClass (Char.ofNat n) == 0 },
  { name := "the combining class of a grave accent is 230", holds := combiningClass (Char.ofNat 0x300) == 230 },
  { name := "the combining class of a virama is 9", holds := combiningClass (Char.ofNat 0x94D) == 9 },
  { name := "the combining class of a supplementary-plane mark is found", holds := combiningClass (Char.ofNat 0x1D165) == 216 },
  { name := "no ASCII character decomposes", holds := (List.range 128).all fun n => (decomposition (Char.ofNat n)).isEmpty },
  { name := "a letter with an accent decomposes into two code points", holds := decomposition (Char.ofNat 0xC0) == cps [0x41, 0x300] },
  { name := "the decomposition is fully expanded", holds := decomposition (Char.ofNat 0x1E09) == cps [0x63, 0x327, 0x301] },
  { name := "a Hangul syllable decomposes algorithmically", holds := decomposition (Char.ofNat 0xAC01) == cps [0x1100, 0x1161, 0x11A8] },
  { name := "a Hangul syllable without a trailing consonant decomposes into two jamo", holds := decomposition (Char.ofNat 0xAC00) == cps [0x1100, 0x1161] },
  { name := "no two ASCII characters compose", holds := (List.range 128).all fun a => (List.range 128).all fun b => (compose (Char.ofNat a) (Char.ofNat b)).isNone },
  { name := "a Hangul leading consonant and a combining mark do not compose", holds := (compose (Char.ofNat 0x1100) (Char.ofNat 0x300)).isNone },
  { name := "a letter below the Hangul jamo and a vowel jamo do not compose", holds := (compose 'a' (Char.ofNat 0x1161)).isNone },
  { name := "a leading consonant and a jamo after the vowels do not compose", holds := (compose (Char.ofNat 0x1100) (Char.ofNat 0x1176)).isNone },
  { name := "a syllable without a trailing consonant and the first trailing jamo do not compose", holds := (compose (Char.ofNat 0xAC00) (Char.ofNat 0x11A7)).isNone },
  { name := "a syllable without a trailing consonant and a jamo after the trailing consonants do not compose", holds := (compose (Char.ofNat 0xAC00) (Char.ofNat 0x11C3)).isNone },
  { name := "a letter and a trailing consonant jamo do not compose", holds := (compose 'a' (Char.ofNat 0x11A8)).isNone },
  { name := "a syllable without a trailing consonant composes with the last trailing jamo", holds := compose (Char.ofNat 0xAC00) (Char.ofNat 0x11C2) == some (Char.ofNat 0xAC1B) },
  { name := "a decomposition line without a code point is rejected", holds := (parseDecompositionLine "C0").isNone },
  { name := "a decomposition line with a bad code point is rejected", holds := (parseDecompositionLine "C0 4G").isNone },
  { name := "a decomposition line with a bad key is rejected", holds := (parseDecompositionLine "ZZ 41").isNone },
  { name := "a decomposition line is read", holds := (parseDecompositionLine "C0 41 300").map (·.value) == some (cps [0x41, 0x300]) },
  { name := "a composition line with a single field is rejected", holds := (parseCompositionLine "41").isNone },
  { name := "a composition line with too many fields is rejected", holds := (parseCompositionLine "41 300 C0 C1").isNone },
  { name := "a composition line with too few fields is rejected", holds := (parseCompositionLine "41 300").isNone },
  { name := "a composition line with a bad first code point is rejected", holds := (parseCompositionLine "Z 300 C0").isNone },
  { name := "a composition line with a bad second code point is rejected", holds := (parseCompositionLine "41 Z C0").isNone },
  { name := "a composition line with a bad composite is rejected", holds := (parseCompositionLine "41 300 Z").isNone },
  { name := "a composition line is read", holds := parseCompositionLine "41 300 C0" == some ((0x41, 0x300), Char.ofNat 0xC0) },
  { name := "code points of an empty list are rejected", holds := (decodeCodePoints []).isNone },
  { name := "a base letter and a combining mark compose", holds := compose 'a' (Char.ofNat 0x300) == some (Char.ofNat 0xE0) },
  { name := "normalization is idempotent on the sample inputs", holds := cases.all fun c => nfc (nfc (cps c.input)) == nfc (cps c.input) },
  { name := "an ASCII string is its own normalization", holds := (List.range 128).all fun n => nfc [Char.ofNat n] == [Char.ofNat n] }
]

/-- info: [] -/
#guard_msgs in
#eval UrllibTest.failedChecks checks

end UrllibTest.Unicode.Normalization
