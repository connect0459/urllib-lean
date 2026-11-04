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

def parseOpaque (input : List Char) : Except Error Host :=
  if input.any isForbiddenHostCodePoint then
    .error .forbiddenHostCodePoint
  else
    .ok (.opaqueHost (PercentEncoding.utf8PercentEncode .c0Control (String.ofList input)))

def domainToAscii (domain : List Char) : Except Error (List Char) :=
  if domain.any (fun (c : Char) => decide (128 ≤ c.toNat)) then
    .error .nonAsciiDomain
  else
    let lowered := domain.map Char.toLower
    if lowered.isEmpty then .error .emptyDomain else .ok lowered

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

def parse (input : String) (isOpaque : Bool) : Except Error Host :=
  parseChars input.toList isOpaque

def serialize : Host → String
  | .domain name => name
  | .ipv4 address => address.serialize
  | .ipv6 address => "[" ++ address.serialize ++ "]"
  | .opaqueHost text => text
  | .empty => ""

end Host

end Urllib
