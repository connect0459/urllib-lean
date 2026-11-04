import Urllib.Host.Ipv4

namespace UrllibTest.Host.Ipv4

open Urllib.Host

inductive Outcome where
  | address (text : String)
  | failure (error : Ipv4Error)
  deriving DecidableEq, Repr

def outcome (input : String) : Outcome :=
  match Ipv4.parse input with
  | .ok address => .address address.serialize
  | .error e => .failure e

structure ParseCase where
  name : String
  input : String
  expected : Outcome

def parseCases : List ParseCase := [
  { name := "parses the all-zero address", input := "0.0.0.0", expected := .address "0.0.0.0" },
  { name := "parses a dotted-decimal address", input := "127.0.0.1", expected := .address "127.0.0.1" },
  { name := "parses a private-range address", input := "192.168.0.1", expected := .address "192.168.0.1" },
  { name := "parses the broadcast address", input := "255.255.255.255", expected := .address "255.255.255.255" },
  { name := "parses a hexadecimal part", input := "0x7f.1", expected := .address "127.0.0.1" },
  { name := "parses an uppercase hexadecimal prefix", input := "0X7F.0.0.1", expected := .address "127.0.0.1" },
  { name := "parses octal parts", input := "0300.0250.0.1", expected := .address "192.168.0.1" },
  { name := "parses a single octal number", input := "017700000001", expected := .address "127.0.0.1" },
  { name := "parses a single decimal number", input := "4294967295", expected := .address "255.255.255.255" },
  { name := "parses a single hexadecimal number", input := "0xffffffff", expected := .address "255.255.255.255" },
  { name := "fills the last part across the remaining bytes with three parts", input := "1.2.3", expected := .address "1.2.0.3" },
  { name := "fills the last part across the remaining bytes with two parts", input := "1.2", expected := .address "1.0.0.2" },
  { name := "accepts a last part above 255 when fewer than four parts are given", input := "1.256", expected := .address "1.0.1.0" },
  { name := "treats a bare hexadecimal prefix as zero", input := "0x", expected := .address "0.0.0.0" },
  { name := "parses a single zero", input := "0", expected := .address "0.0.0.0" },
  { name := "parses a doubled zero as octal zero", input := "00", expected := .address "0.0.0.0" },
  { name := "ignores one trailing dot", input := "1.2.3.4.", expected := .address "1.2.3.4" },
  { name := "rejects empty input", input := "", expected := .failure .nonNumericPart },
  { name := "rejects a lone dot", input := ".", expected := .failure .nonNumericPart },
  { name := "rejects an empty middle part", input := "1..2", expected := .failure .nonNumericPart },
  { name := "rejects a digit outside the octal range", input := "08", expected := .failure .nonNumericPart },
  { name := "rejects a non-hexadecimal digit after the hexadecimal prefix", input := "0xg", expected := .failure .nonNumericPart },
  { name := "rejects letters", input := "a.b", expected := .failure .nonNumericPart },
  { name := "rejects a sign", input := "-1", expected := .failure .nonNumericPart },
  { name := "rejects more than four parts", input := "1.2.3.4.5", expected := .failure .tooManyParts },
  { name := "rejects two trailing dots", input := "1.2.3.4..", expected := .failure .tooManyParts },
  { name := "rejects a non-last part above 255", input := "256.1", expected := .failure .outOfRange },
  { name := "rejects a fourth part above 255", input := "1.2.3.256", expected := .failure .outOfRange },
  { name := "rejects a single number above the 32-bit range", input := "4294967296", expected := .failure .outOfRange }
]

def parseFailures : List String :=
  parseCases.filterMap fun c => if outcome c.input == c.expected then none else some c.name

/-- info: [] -/
#guard_msgs in
#eval parseFailures

structure NumberCase where
  name : String
  input : String
  expected : Bool

def endsInNumberCases : List NumberCase := [
  { name := "a plain domain does not end in a number", input := "example.com", expected := false },
  { name := "a decimal last label ends in a number", input := "example.123", expected := true },
  { name := "a hexadecimal last label ends in a number", input := "example.0x1f", expected := true },
  { name := "a dotted quad ends in a number", input := "1.2.3.4", expected := true },
  { name := "a malformed hexadecimal last label does not end in a number", input := "example.0xg", expected := false },
  { name := "an all-digit label with an invalid octal digit still ends in a number", input := "a.b.09", expected := true },
  { name := "a trailing dot is ignored", input := "123.", expected := true },
  { name := "a trailing dot after a word is ignored", input := "x.", expected := false },
  { name := "a lone dot does not end in a number", input := ".", expected := false },
  { name := "an empty host does not end in a number", input := "", expected := false },
  { name := "a bare hexadecimal prefix ends in a number", input := "0x", expected := true },
  { name := "an octal-looking label ends in a number", input := "x.017", expected := true }
]

def endsInNumberFailures : List String :=
  endsInNumberCases.filterMap fun c =>
    if Ipv4.endsInNumber c.input == c.expected then none else some c.name

/-- info: [] -/
#guard_msgs in
#eval endsInNumberFailures

#guard (Ipv4.mk 0).serialize == "0.0.0.0"
#guard (Ipv4.mk 0x7F000001).serialize == "127.0.0.1"
#guard (Ipv4.mk 0xFFFFFFFF).serialize == "255.255.255.255"
#guard (Ipv4.mk 0x01020304).serialize == "1.2.3.4"

end UrllibTest.Host.Ipv4
