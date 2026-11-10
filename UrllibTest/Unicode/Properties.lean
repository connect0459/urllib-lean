import UrllibTest.Support
import Urllib.Unicode.Properties

namespace UrllibTest.Unicode.Properties

open Urllib.Unicode

def checks : List UrllibTest.Check := [
  { name := "a combining grave accent is a mark", holds := isMark (Char.ofNat 0x300) },
  { name := "a Latin letter is not a mark", holds := !isMark 'a' },
  { name := "no code point below U+0300 is a mark in the table", holds := (List.range 0x300).all fun n => (lookup? markTable n).isNone },
  { name := "no code point below U+0590 is right-to-left or an Arabic number in the table", holds := (List.range 0x590).all fun n => match bidiClass (Char.ofNat n) with | .r | .al | .an => false | _ => true },
  { name := "a supplementary-plane mark is found", holds := isMark (Char.ofNat 0x1D165) },
  { name := "a Latin letter is left-to-right", holds := bidiClass 'a' == .l },
  { name := "a Hebrew letter is right-to-left", holds := bidiClass (Char.ofNat 0x5D0) == .r },
  { name := "an Arabic letter has the Arabic letter class", holds := bidiClass (Char.ofNat 0x627) == .al },
  { name := "an Arabic-Indic digit is an Arabic number", holds := bidiClass (Char.ofNat 0x660) == .an },
  { name := "a European digit is a European number", holds := bidiClass '5' == .en },
  { name := "a plus sign is a European separator", holds := bidiClass '+' == .es },
  { name := "a percent sign is a European terminator", holds := bidiClass '%' == .et },
  { name := "a comma is a common separator", holds := bidiClass ',' == .cs },
  { name := "a combining mark is a nonspacing mark", holds := bidiClass (Char.ofNat 0x300) == .nsm },
  { name := "a control character is boundary neutral", holds := bidiClass (Char.ofNat 1) == .bn },
  { name := "a line feed is a paragraph separator", holds := bidiClass '\n' == .b },
  { name := "a tab is a segment separator", holds := bidiClass '\t' == .s },
  { name := "a space is whitespace", holds := bidiClass ' ' == .ws },
  { name := "an exclamation mark is another neutral", holds := bidiClass '!' == .on },
  { name := "a left-to-right embedding is an explicit formatting class", holds := bidiClass (Char.ofNat 0x202A) == .other },
  { name := "an Arabic letter joins on both sides", holds := joiningType (Char.ofNat 0x628) == .dualJoining },
  { name := "an alef joins on the right", holds := joiningType (Char.ofNat 0x627) == .rightJoining },
  { name := "a Mongolian letter joins on the left", holds := joiningType (Char.ofNat 0xA872) == .leftJoining },
  { name := "a combining mark is transparent", holds := joiningType (Char.ofNat 0x300) == .transparent },
  { name := "a Latin letter does not join", holds := joiningType 'a' == .none },
  { name := "an ASCII letter starts and continues an identifier", holds := isIdStart 'a' && isIdContinue 'a' },
  { name := "a digit continues but does not start an identifier", holds := !isIdStart '5' && isIdContinue '5' },
  { name := "an underscore and a dollar sign are not ID_Start or ID_Continue letters", holds := !isIdStart '$' && !isIdStart '_' && isIdContinue '_' && !isIdContinue '$' },
  { name := "a letter outside ASCII starts an identifier", holds := isIdStart (Char.ofNat 0x20000) && isIdStart (Char.ofNat 0x3400) && isIdStart (Char.ofNat 0x2118) },
  { name := "an emoji does not start an identifier", holds := !isIdStart (Char.ofNat 0x1F6B2) && !isIdContinue (Char.ofNat 0x1F6B2) },
  { name := "a combining mark continues but does not start an identifier", holds := !isIdStart (Char.ofNat 0x300) && isIdContinue (Char.ofNat 0x300) },
  { name := "a bidi payload decodes to its class", holds := decodeBidi ["AL"] == some .al },
  { name := "a bidi payload of several words is rejected", holds := (decodeBidi ["AL", "R"]).isNone },
  { name := "a joining payload decodes to its type", holds := decodeJoining ["D"] == some .dualJoining },
  { name := "a joining payload of several words is rejected", holds := (decodeJoining []).isNone },
  { name := "an unknown bidi name is an explicit formatting class", holds := BidiClass.ofName "LRE" == .other },
  { name := "an unknown joining name is none", holds := JoiningType.ofName "C" == .none }
]

/-- info: [] -/
#guard_msgs in
#eval UrllibTest.failedChecks checks

end UrllibTest.Unicode.Properties
