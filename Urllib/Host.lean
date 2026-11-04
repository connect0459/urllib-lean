import Urllib.Host.Ipv4
import Urllib.Host.Ipv6
import Urllib.PercentEncoding

namespace Urllib

/-- A parsed host. -/
inductive Host where
  /-- A domain: lowercase ASCII. -/
  | domain (name : String)
  /-- An IPv4 address. -/
  | ipv4 (address : Host.Ipv4)
  /-- An IPv6 address. -/
  | ipv6 (address : Host.Ipv6)
  /-- An opaque host of a non-special URL, percent-encoded with the C0 control set. -/
  | opaqueHost (text : String)
  /-- The empty host. -/
  | empty
  deriving DecidableEq, Repr

namespace Host

/-- Reasons why the host parser rejects its input. -/
inductive Error where
  /-- The input starts with `[` but does not end with `]`. -/
  | unclosedBracket
  /-- The input ends in a number but is not a valid IPv4 address. -/
  | ipv4 (error : Ipv4Error)
  /-- The bracketed input is not a valid IPv6 address. -/
  | ipv6 (error : Ipv6Error)
  /-- An opaque host contains a forbidden host code point. -/
  | forbiddenHostCodePoint
  /-- A domain contains a forbidden domain code point. -/
  | forbiddenDomainCodePoint
  /-- A domain contains a non-ASCII code point; domain-to-ASCII processing is not implemented. -/
  | nonAsciiDomain
  /-- The domain is empty after processing. -/
  | emptyDomain
  deriving DecidableEq, Repr

/-- Whether `c` is a forbidden host code point. -/
def isForbiddenHostCodePoint (c : Char) : Bool :=
  c.toNat == 0 ||
  [Char.ofNat 9, Char.ofNat 10, Char.ofNat 13, ' ', '#', '/', ':', '<', '>', '?', '@', '[', '\\', ']', '^', '|'].contains c

/-- Whether `c` is a forbidden domain code point. -/
def isForbiddenDomainCodePoint (c : Char) : Bool :=
  isForbiddenHostCodePoint c || c.toNat ≤ 0x1F || c == '%' || c.toNat == 0x7F

/-- The opaque-host parser. -/
def parseOpaque (input : List Char) : Except Error Host :=
  if input.any isForbiddenHostCodePoint then
    .error .forbiddenHostCodePoint
  else
    .ok (.opaqueHost (PercentEncoding.utf8PercentEncode .c0Control (String.ofList input)))

/-- Domain to ASCII without UTS #46: rejects non-ASCII input and lowercases ASCII letters; `xn--` labels pass through unchanged. -/
def domainToAscii (domain : List Char) : Except Error (List Char) :=
  if domain.any (fun (c : Char) => decide (128 ≤ c.toNat)) then
    .error .nonAsciiDomain
  else
    let lowered := domain.map Char.toLower
    if lowered.isEmpty then .error .emptyDomain else .ok lowered

/-- Parses a domain: percent-decodes, converts to ASCII, checks forbidden code points, and returns an IPv4 address when the domain ends in a number. -/
def parseDomain (input : List Char) : Except Error Host := do
  let domain := PercentEncoding.utf8DecodeWithoutBom
    (PercentEncoding.percentDecodeString (String.ofList input))
  let asciiDomain ← domainToAscii domain.toList
  if asciiDomain.any isForbiddenDomainCodePoint then throw .forbiddenDomainCodePoint
  if Ipv4.endsInNumber (String.ofList asciiDomain) then
    let address ← (Ipv4.parse (String.ofList asciiDomain)).mapError Error.ipv4
    return .ipv4 address
  else
    return .domain (String.ofList asciiDomain)

/-- The host parser on characters. -/
def parseChars (input : List Char) (isOpaque : Bool) : Except Error Host :=
  match input with
  | '[' :: rest =>
    if rest.getLast? = some ']' then
      match Ipv6.parse (String.ofList rest.dropLast) with
      | .ok address => .ok (.ipv6 address)
      | .error e => .error (.ipv6 e)
    else
      .error .unclosedBracket
  | _ => if isOpaque then parseOpaque input else parseDomain input

/-- The host parser of the URL Standard; `isOpaque` selects the opaque-host parser for non-special URLs. -/
def parse (input : String) (isOpaque : Bool) : Except Error Host :=
  parseChars input.toList isOpaque

/-- The host serializer; IPv6 addresses are enclosed in brackets. -/
def serialize : Host → String
  | .domain name => name
  | .ipv4 address => address.serialize
  | .ipv6 address => "[" ++ address.serialize ++ "]"
  | .opaqueHost text => text
  | .empty => ""

end Host

end Urllib
