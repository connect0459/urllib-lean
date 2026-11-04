import Urllib.Host.Ipv4
import Urllib.Host.Ipv6
import Urllib.PercentEncoding

namespace Urllib

inductive Host where
  | domain (name : String)
  | ipv4 (address : Host.Ipv4)
  | ipv6 (address : Host.Ipv6)
  | opaqueHost (text : String)
  | empty
  deriving DecidableEq, Repr

namespace Host

inductive Error where
  | unclosedBracket
  | ipv4 (error : Ipv4Error)
  | ipv6 (error : Ipv6Error)
  | forbiddenHostCodePoint
  | forbiddenDomainCodePoint
  | nonAsciiDomain
  | emptyDomain
  deriving DecidableEq, Repr

def isForbiddenHostCodePoint (c : Char) : Bool :=
  c.toNat == 0 ||
  [Char.ofNat 9, Char.ofNat 10, Char.ofNat 13, ' ', '#', '/', ':', '<', '>', '?', '@', '[', '\\', ']', '^', '|'].contains c

def isForbiddenDomainCodePoint (c : Char) : Bool :=
  isForbiddenHostCodePoint c || c.toNat ≤ 0x1F || c == '%' || c.toNat == 0x7F

def parseOpaque (input : String) : Except Error Host :=
  if input.any isForbiddenHostCodePoint then
    .error .forbiddenHostCodePoint
  else
    .ok (.opaqueHost (PercentEncoding.utf8PercentEncode .c0Control input))

def domainToAscii (domain : String) : Except Error String :=
  if domain.any (fun (c : Char) => decide (128 ≤ c.toNat)) then
    .error .nonAsciiDomain
  else
    let lowered := domain.map Char.toLower
    if lowered.isEmpty then .error .emptyDomain else .ok lowered

def parse (input : String) (isOpaque : Bool) : Except Error Host := do
  if input.startsWith "[" then
    if !input.endsWith "]" then throw .unclosedBracket
    let inner := String.ofList (input.toList.drop 1).dropLast
    let address ← (Ipv6.parse inner).mapError Error.ipv6
    return .ipv6 address
  else if isOpaque then
    parseOpaque input
  else
    let domain := PercentEncoding.utf8DecodeWithoutBom (PercentEncoding.percentDecodeString input)
    let asciiDomain ← domainToAscii domain
    if asciiDomain.any isForbiddenDomainCodePoint then throw .forbiddenDomainCodePoint
    if Ipv4.endsInNumber asciiDomain then
      let address ← (Ipv4.parse asciiDomain).mapError Error.ipv4
      return .ipv4 address
    else
      return .domain asciiDomain

def serialize : Host → String
  | .domain name => name
  | .ipv4 address => address.serialize
  | .ipv6 address => "[" ++ address.serialize ++ "]"
  | .opaqueHost text => text
  | .empty => ""

end Host

end Urllib
