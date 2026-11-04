import UrllibTest.Support
import Urllib.Host

namespace UrllibTest.Host

open Urllib

inductive Outcome where
  | host (text : String)
  | failure (error : Host.Error)
  deriving DecidableEq, Repr

def outcome (input : String) (isOpaque : Bool) : Outcome :=
  match Host.parse input isOpaque with
  | .ok host => .host host.serialize
  | .error e => .failure e

structure ParseCase where
  name : String
  input : String
  isOpaque : Bool
  expected : Outcome

def domainCases : List ParseCase := [
  { name := "keeps a lowercase domain", input := "example.com", isOpaque := false, expected := .host "example.com" },
  { name := "lowercases an ASCII domain", input := "ExAmPlE.CoM", isOpaque := false, expected := .host "example.com" },
  { name := "keeps a trailing dot", input := "example.com.", isOpaque := false, expected := .host "example.com." },
  { name := "percent-decodes the domain", input := "a%62c.com", isOpaque := false, expected := .host "abc.com" },
  { name := "passes an ASCII xn-- label through unchanged", input := "XN--nxasmq6b.example", isOpaque := false, expected := .host "xn--nxasmq6b.example" },
  { name := "rejects an empty domain", input := "", isOpaque := false, expected := .failure .emptyDomain },
  { name := "rejects a non-ASCII domain", input := "é.com", isOpaque := false, expected := .failure .nonAsciiDomain },
  { name := "rejects a percent-encoded non-ASCII domain", input := "%C3%A9.com", isOpaque := false, expected := .failure .nonAsciiDomain },
  { name := "rejects a percent-encoded invalid UTF-8 domain", input := "%FF.com", isOpaque := false, expected := .failure .nonAsciiDomain },
  { name := "rejects a space", input := "exa mple.org", isOpaque := false, expected := .failure .forbiddenDomainCodePoint },
  { name := "rejects a number sign", input := "a#b", isOpaque := false, expected := .failure .forbiddenDomainCodePoint },
  { name := "rejects a slash", input := "a/b", isOpaque := false, expected := .failure .forbiddenDomainCodePoint },
  { name := "rejects a colon", input := "a:b", isOpaque := false, expected := .failure .forbiddenDomainCodePoint },
  { name := "rejects a less-than sign", input := "a<b", isOpaque := false, expected := .failure .forbiddenDomainCodePoint },
  { name := "rejects a greater-than sign", input := "a>b", isOpaque := false, expected := .failure .forbiddenDomainCodePoint },
  { name := "rejects a question mark", input := "a?b", isOpaque := false, expected := .failure .forbiddenDomainCodePoint },
  { name := "rejects an at sign", input := "a@b", isOpaque := false, expected := .failure .forbiddenDomainCodePoint },
  { name := "rejects a left bracket", input := "a[b", isOpaque := false, expected := .failure .forbiddenDomainCodePoint },
  { name := "rejects a backslash", input := "a\\b", isOpaque := false, expected := .failure .forbiddenDomainCodePoint },
  { name := "rejects a right bracket", input := "a]b", isOpaque := false, expected := .failure .forbiddenDomainCodePoint },
  { name := "rejects a caret", input := "a^b", isOpaque := false, expected := .failure .forbiddenDomainCodePoint },
  { name := "rejects a vertical bar", input := "a|b", isOpaque := false, expected := .failure .forbiddenDomainCodePoint },
  { name := "rejects a literal percent sign that is not an escape", input := "a%b", isOpaque := false, expected := .failure .forbiddenDomainCodePoint },
  { name := "rejects a percent sign produced by decoding", input := "a%25b", isOpaque := false, expected := .failure .forbiddenDomainCodePoint },
  { name := "rejects a NUL produced by decoding", input := "a%00b", isOpaque := false, expected := .failure .forbiddenDomainCodePoint },
  { name := "rejects a DEL produced by decoding", input := "a%7Fb", isOpaque := false, expected := .failure .forbiddenDomainCodePoint },
  { name := "rejects a C0 control produced by decoding", input := "a%01b", isOpaque := false, expected := .failure .forbiddenDomainCodePoint }
]

def ipv4Cases : List ParseCase := [
  { name := "parses a dotted-decimal IPv4 host", input := "127.0.0.1", isOpaque := false, expected := .host "127.0.0.1" },
  { name := "parses a hexadecimal IPv4 host", input := "0x7f.1", isOpaque := false, expected := .host "127.0.0.1" },
  { name := "parses an octal IPv4 host", input := "0300.0250.0.1", isOpaque := false, expected := .host "192.168.0.1" },
  { name := "fills the last part of a short IPv4 host", input := "1.2.3", isOpaque := false, expected := .host "1.2.0.3" },
  { name := "parses a percent-encoded IPv4 host", input := "%31%32%37.0.0.1", isOpaque := false, expected := .host "127.0.0.1" },
  { name := "parses a single-number IPv4 host", input := "2130706433", isOpaque := false, expected := .host "127.0.0.1" },
  { name := "rejects an out-of-range IPv4 part", input := "256.256.256.256", isOpaque := false, expected := .failure (.ipv4 .outOfRange) },
  { name := "rejects an IPv4 host with too many parts", input := "1.2.3.4.5", isOpaque := false, expected := .failure (.ipv4 .tooManyParts) },
  { name := "treats a domain whose last label is a malformed number as a domain", input := "example.0x1f.0xg", isOpaque := false, expected := .host "example.0x1f.0xg" },
  { name := "rejects a domain whose last label is a number", input := "example.123", isOpaque := false, expected := .failure (.ipv4 .nonNumericPart) },
  { name := "rejects a number above 32 bits", input := "999999999999", isOpaque := false, expected := .failure (.ipv4 .outOfRange) }
]

def ipv6Cases : List ParseCase := [
  { name := "parses the IPv6 loopback host", input := "[::1]", isOpaque := false, expected := .host "[::1]" },
  { name := "parses a full IPv6 host", input := "[1:2:3:4:5:6:7:8]", isOpaque := false, expected := .host "[1:2:3:4:5:6:7:8]" },
  { name := "lowercases an IPv6 host", input := "[2001:DB8::1]", isOpaque := false, expected := .host "[2001:db8::1]" },
  { name := "parses an IPv6 host even for an opaque host", input := "[::1]", isOpaque := true, expected := .host "[::1]" },
  { name := "rejects an unclosed bracket", input := "[::1", isOpaque := false, expected := .failure .unclosedBracket },
  { name := "rejects an unclosed bracket for an opaque host", input := "[::1", isOpaque := true, expected := .failure .unclosedBracket },
  { name := "rejects an IPv6 host with too few pieces", input := "[1:2]", isOpaque := false, expected := .failure (.ipv6 .tooFewPieces) },
  { name := "rejects empty brackets", input := "[]", isOpaque := false, expected := .failure (.ipv6 .tooFewPieces) }
]

def opaqueCases : List ParseCase := [
  { name := "keeps an opaque host as written", input := "ExAmPlE.com", isOpaque := true, expected := .host "ExAmPlE.com" },
  { name := "allows an empty opaque host", input := "", isOpaque := true, expected := .host "" },
  { name := "percent-encodes non-ASCII code points in an opaque host", input := "é", isOpaque := true, expected := .host "%C3%A9" },
  { name := "keeps existing escapes in an opaque host", input := "%41", isOpaque := true, expected := .host "%41" },
  { name := "allows a percent sign in an opaque host", input := "a%b", isOpaque := true, expected := .host "a%b" },
  { name := "does not interpret numbers in an opaque host", input := "0x7f.1", isOpaque := true, expected := .host "0x7f.1" },
  { name := "rejects a space in an opaque host", input := "a b", isOpaque := true, expected := .failure .forbiddenHostCodePoint },
  { name := "rejects a less-than sign in an opaque host", input := "a<b", isOpaque := true, expected := .failure .forbiddenHostCodePoint },
  { name := "rejects a slash in an opaque host", input := "a/b", isOpaque := true, expected := .failure .forbiddenHostCodePoint }
]

def parseFailures (cases : List ParseCase) : List String :=
  cases.filterMap fun c =>
    if outcome c.input c.isOpaque == c.expected then none else some c.name

/-- info: [] -/
#guard_msgs in
#eval parseFailures domainCases

/-- info: [] -/
#guard_msgs in
#eval parseFailures ipv4Cases

/-- info: [] -/
#guard_msgs in
#eval parseFailures ipv6Cases

/-- info: [] -/
#guard_msgs in
#eval parseFailures opaqueCases

def guardChecks : List UrllibTest.Check := [
  { name := "parses a plain domain into a domain host", holds := match Host.parse "example.com" false with | .ok (.domain name) => name == "example.com" | _ => false },
  { name := "parses a dotted-decimal host into the matching IPv4 value", holds := match Host.parse "127.0.0.1" false with | .ok (.ipv4 address) => address.value == 0x7F000001 | _ => false },
  { name := "parses a bracketed host into an IPv6 host", holds := match Host.parse "[::1]" false with | .ok (.ipv6 _) => true | _ => false },
  { name := "rejects a space in an opaque host with the forbidden host code point error", holds := match Host.parse "a b" true with | .error .forbiddenHostCodePoint => true | _ => false },
  { name := "parses an opaque host into an opaque host", holds := match Host.parse "ab" true with | .ok (.opaqueHost text) => text == "ab" | _ => false },
  { name := "serializes the empty host to the empty string", holds := Host.serialize .empty == "" }
]

/-- info: [] -/
#guard_msgs in
#eval UrllibTest.failedChecks guardChecks

end UrllibTest.Host
