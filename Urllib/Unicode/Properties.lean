import Urllib.Unicode.Table
import Urllib.Unicode.Data.Properties
import Urllib.Unicode.Data.Normalization

namespace Urllib.Unicode

/-- The Bidi_Class values of UAX #9. -/
inductive BidiClass where
  /-- Left-to-right. -/
  | l
  /-- Right-to-left. -/
  | r
  /-- Arabic letter. -/
  | al
  /-- European number. -/
  | en
  /-- European separator. -/
  | es
  /-- European terminator. -/
  | et
  /-- Arabic number. -/
  | an
  /-- Common separator. -/
  | cs
  /-- Nonspacing mark. -/
  | nsm
  /-- Boundary neutral. -/
  | bn
  /-- Paragraph separator. -/
  | b
  /-- Segment separator. -/
  | s
  /-- Whitespace. -/
  | ws
  /-- Other neutral. -/
  | on
  /-- Any explicit directional formatting class. -/
  | other
  deriving DecidableEq, Repr

/-- Reads a Bidi_Class name. -/
def BidiClass.ofName : String → BidiClass
  | "L" => .l
  | "R" => .r
  | "AL" => .al
  | "EN" => .en
  | "ES" => .es
  | "ET" => .et
  | "AN" => .an
  | "CS" => .cs
  | "NSM" => .nsm
  | "BN" => .bn
  | "B" => .b
  | "S" => .s
  | "WS" => .ws
  | "ON" => .on
  | _ => .other

/-- The Joining_Type values that matter to the ZERO WIDTH NON-JOINER rule; every other value is `none`. -/
inductive JoiningType where
  /-- Left-joining. -/
  | leftJoining
  /-- Right-joining. -/
  | rightJoining
  /-- Dual-joining. -/
  | dualJoining
  /-- Transparent. -/
  | transparent
  /-- Any other joining type. -/
  | none
  deriving DecidableEq, Repr

/-- Reads a Joining_Type abbreviation. -/
def JoiningType.ofName : String → JoiningType
  | "L" => .leftJoining
  | "R" => .rightJoining
  | "D" => .dualJoining
  | "T" => .transparent
  | _ => .none

/-- Decodes a Bidi_Class payload. -/
def decodeBidi (fields : List String) : Option BidiClass :=
  (decodeName fields).map BidiClass.ofName

/-- Decodes a Joining_Type payload. -/
def decodeJoining (fields : List String) : Option JoiningType :=
  (decodeName fields).map JoiningType.ofName

/-- The ranges of General_Category Mark. -/
def markTable : Array (Range Unit) := parseTable decodeUnit Data.markRanges

/-- The Bidi_Class ranges. -/
def bidiTable : Array (Range BidiClass) :=
  parseTable decodeBidi Data.bidiClasses

/-- The Joining_Type ranges. -/
def joiningTable : Array (Range JoiningType) :=
  parseTable decodeJoining Data.joiningTypes

/-- The Canonical_Combining_Class ranges for the non-zero classes. -/
def combiningClassTable : Array (Range Nat) := parseTable decodeNat Data.combiningClasses

/-- Whether `c` has General_Category Mark; no mark is below U+0300. -/
def isMark (c : Char) : Bool :=
  0x300 ≤ c.toNat && (lookup? markTable c.toNat).isSome

/-- The Bidi_Class of `c`. -/
def bidiClass (c : Char) : BidiClass :=
  (lookup? bidiTable c.toNat).getD .l

/-- The Joining_Type of `c`. -/
def joiningType (c : Char) : JoiningType :=
  (lookup? joiningTable c.toNat).getD .none

/-- The Canonical_Combining_Class of `c`; no character below U+0300 has a non-zero class. -/
def combiningClass (c : Char) : Nat :=
  if c.toNat < 0x300 then 0 else (lookup? combiningClassTable c.toNat).getD 0

end Urllib.Unicode
