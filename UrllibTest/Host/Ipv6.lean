import UrllibTest.Support
import Urllib.Host.Ipv6

namespace UrllibTest.Host.Ipv6

open Urllib.Host

inductive Outcome where
  | address (text : String)
  | failure (error : Ipv6Error)
  deriving DecidableEq, Repr

def outcome (input : String) : Outcome :=
  match Ipv6.parse input with
  | .ok address => .address address.serialize
  | .error e => .failure e

structure ParseCase where
  name : String
  input : String
  expected : Outcome

def parseCases : List ParseCase := [
  { name := "parses the unspecified address", input := "::", expected := .address "::" },
  { name := "parses the loopback address", input := "::1", expected := .address "::1" },
  { name := "parses a trailing compression", input := "1::", expected := .address "1::" },
  { name := "parses a middle compression", input := "1::8", expected := .address "1::8" },
  { name := "parses eight explicit pieces", input := "1:2:3:4:5:6:7:8", expected := .address "1:2:3:4:5:6:7:8" },
  { name := "parses the largest pieces", input := "ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff", expected := .address "ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff" },
  { name := "parses mixed-case hexadecimal digits and serializes them in lowercase", input := "2001:DB8::1", expected := .address "2001:db8::1" },
  { name := "parses leading zeros within a piece", input := "0001::", expected := .address "1::" },
  { name := "compresses a leading run of zeros when serializing", input := "0:0:0:0:0:0:0:1", expected := .address "::1" },
  { name := "compresses the first of two equally long zero runs", input := "2001:db8:0:0:1:0:0:1", expected := .address "2001:db8::1:0:0:1" },
  { name := "compresses the longest zero run", input := "1:0:0:2:0:0:0:3", expected := .address "1:0:0:2::3" },
  { name := "does not compress a single zero piece", input := "0:1:0:1:0:1:0:1", expected := .address "0:1:0:1:0:1:0:1" },
  { name := "does not compress a single trailing zero produced by a trailing compression", input := "1:2:3:4:5:6:7::", expected := .address "1:2:3:4:5:6:7:0" },
  { name := "does not compress a single leading zero produced by a leading compression", input := "::2:3:4:5:6:7:8", expected := .address "0:2:3:4:5:6:7:8" },
  { name := "compresses a run between pieces", input := "1:0:0:0:0:0:0:1", expected := .address "1::1" },
  { name := "compresses the first run when it is not at the start", input := "0:0:1:0:0:0:1:0", expected := .address "0:0:1::1:0" },
  { name := "parses an embedded IPv4 address after a compression", input := "::1.2.3.4", expected := .address "::102:304" },
  { name := "parses an embedded IPv4 address after six pieces", input := "1:2:3:4:5:6:1.2.3.4", expected := .address "1:2:3:4:5:6:102:304" },
  { name := "serializes an IPv4-mapped address in hexadecimal", input := "::ffff:192.0.2.128", expected := .address "::ffff:c000:280" },
  { name := "parses an embedded all-zero IPv4 address", input := "::0.0.0.0", expected := .address "::" },
  { name := "rejects a single leading colon", input := ":1", expected := .failure .invalidCompression },
  { name := "rejects a lone colon", input := ":", expected := .failure .invalidCompression },
  { name := "rejects a trailing single colon", input := "1:", expected := .failure .invalidCodePoint },
  { name := "rejects fewer than eight pieces without a compression", input := "1:2:3:4:5:6:7", expected := .failure .tooFewPieces },
  { name := "rejects a single piece", input := "1", expected := .failure .tooFewPieces },
  { name := "rejects more than eight pieces", input := "1:2:3:4:5:6:7:8:9", expected := .failure .tooManyPieces },
  { name := "rejects two compressions", input := "1::2::3", expected := .failure .multipleCompression },
  { name := "rejects a piece with more than four digits", input := "12345::", expected := .failure .invalidCodePoint },
  { name := "rejects a non-hexadecimal character", input := "g::", expected := .failure .invalidCodePoint },
  { name := "rejects an IPv4 address with too few parts", input := "::1.2.3", expected := .failure .ipv4InIpv6TooFewParts },
  { name := "rejects an IPv4 address without a leading compression", input := "1.2.3.4", expected := .failure .tooFewPieces },
  { name := "rejects an embedded IPv4 address that starts with a dot", input := "::.1.2.3", expected := .failure .ipv4InIpv6InvalidCodePoint },
  { name := "rejects an embedded IPv4 address in the eighth piece", input := "1:2:3:4:5:6:7:1.2.3.4", expected := .failure .ipv4InIpv6TooManyPieces },
  { name := "rejects an embedded IPv4 part above 255", input := "::1.2.3.256", expected := .failure .ipv4InIpv6OutOfRangePart },
  { name := "rejects an embedded IPv4 part with a leading zero", input := "::01.2.3.4", expected := .failure .ipv4InIpv6InvalidCodePoint },
  { name := "rejects a fifth embedded IPv4 part", input := "::1.2.3.4.5", expected := .failure .ipv4InIpv6InvalidCodePoint },
  { name := "rejects an empty embedded IPv4 part", input := "::1..2.3", expected := .failure .ipv4InIpv6InvalidCodePoint },
  { name := "rejects a non-digit embedded IPv4 part", input := "::1.2.3.a", expected := .failure .ipv4InIpv6InvalidCodePoint },
  { name := "rejects a colon after an embedded IPv4 address", input := "::1.2.3.4:5", expected := .failure .ipv4InIpv6InvalidCodePoint },
  { name := "rejects empty input", input := "", expected := .failure .tooFewPieces },
  { name := "rejects a trailing dot after an embedded IPv4 part", input := "::1.2.3.", expected := .failure .ipv4InIpv6InvalidCodePoint }
]

def parseFailures : List String :=
  parseCases.filterMap fun c => if outcome c.input == c.expected then none else some c.name

/-- info: [] -/
#guard_msgs in
#eval parseFailures

def zeroRunPattern (mask : Nat) : Ipv6 :=
  Ipv6.ofPieces ((List.range 8).map fun i =>
    if mask / 2 ^ i % 2 = 1 then 0 else (i + 1) * 0x1111)

/-- info: [] -/
#guard_msgs in
#eval (List.range 256).filter fun mask =>
  (Ipv6.parse (zeroRunPattern mask).serialize).toOption != some (zeroRunPattern mask)

def guardChecks : List UrllibTest.Check := [
  { name := "reads no digits as zero when the next character is not a digit",
    holds := match Ipv6.readDecimalPiece none ['x'] with
      | .ok (piece, rest) => piece == 0 && rest == ['x']
      | .error _ => false },
  { name := "reads no digits as zero at the end of input",
    holds := match Ipv6.readDecimalPiece none [] with
      | .ok (piece, rest) => piece == 0 && rest.isEmpty
      | .error _ => false },
  { name := "fails when the input outlasts the fuel of the piece loop",
    holds := match Ipv6.parseLoop 0 {} ['1'] with
      | .error .invalidCodePoint => true
      | _ => false },
  { name := "fails when the embedded IPv4 input outlasts the fuel",
    holds := match Ipv6.readIpv4Parts 0 {} 0 ['1'] with
      | .error .ipv4InIpv6InvalidCodePoint => true
      | _ => false }
]

/-- info: [] -/
#guard_msgs in
#eval UrllibTest.failedChecks guardChecks

end UrllibTest.Host.Ipv6
