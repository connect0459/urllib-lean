import Urllib.UrlPattern.Parser
import Urllib.Url.Setters

namespace Urllib.UrlPattern

open Urllib.Url

/-- The dummy URL that the canonicalization algorithms modify. -/
def dummyUrl : Url :=
  { scheme := "https", username := "", password := "", host := some (.domain "dummy.invalid"), port := none,
    path := .list [""], query := none, fragment := none }

/-- Canonicalizes a protocol. -/
def canonicalizeProtocol (value : String) : Except Error String :=
  if value.isEmpty then .ok value
  else
    match parse (value ++ "://dummy.invalid/") none with
    | .ok url => .ok url.scheme
    | .error _ => .error .canonicalize

/-- Canonicalizes a username. -/
def canonicalizeUsername (value : String) : Except Error String :=
  if value.isEmpty then .ok value else .ok (dummyUrl.setUsername value).username

/-- Canonicalizes a password. -/
def canonicalizePassword (value : String) : Except Error String :=
  if value.isEmpty then .ok value else .ok (dummyUrl.setPassword value).password

/-- Canonicalizes a hostname. -/
def canonicalizeHostname (value : String) : Except Error String :=
  if value.isEmpty then .ok value
  else
    match parseWithOverrideStrict dummyUrl value .hostname with
    | .ok url => .ok (match url.host with | some h => h.serialize | none => "")
    | .error _ => .error .canonicalize

/-- Canonicalizes an IPv6 hostname: only hexadecimal digits, brackets, and colons are allowed, in lowercase. -/
def canonicalizeIpv6Hostname (value : String) : Except Error String :=
  if value.toList.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F') || c == '[' || c == ']' || c == ':' then
    .ok (String.ofList (value.toList.map Char.toLower))
  else .error .canonicalize

/-- Canonicalizes a port; the protocol, when given, lets the parser drop a default port. -/
def canonicalizePort (value : String) (protocol : Option String := none) : Except Error String :=
  if value.isEmpty then .ok value
  else
    let dummy := { dummyUrl with scheme := protocol.getD "" }
    match parseWithOverrideStrict dummy value .port with
    | .ok url => .ok url.portText
    | .error _ => .error .canonicalize

/-- Canonicalizes a pathname or a piece of one. -/
def canonicalizePathname (value : String) : Except Error String :=
  if value.isEmpty then .ok value
  else
    let leadingSlash := value.startsWith "/"
    let modified := if leadingSlash then value else "/-" ++ value
    let url := parseWithOverride { dummyUrl with path := .list [] } modified .pathStart
    let result := serializePath url.path
    .ok (if leadingSlash then result else (result.drop 2).toString)

/-- Canonicalizes an opaque pathname. -/
def canonicalizeOpaquePathname (value : String) : Except Error String :=
  if value.isEmpty then .ok value
  else
    match parseWithOverrideStrict { dummyUrl with path := .opaque "" } value .opaquePath with
    | .ok url => .ok (serializePath url.path)
    | .error _ => .error .canonicalize

/-- Canonicalizes a search. -/
def canonicalizeSearch (value : String) : Except Error String :=
  if value.isEmpty then .ok value
  else .ok ((parseWithOverride { dummyUrl with query := some "" } value .query).query.getD "")

/-- Canonicalizes a hash. -/
def canonicalizeHash (value : String) : Except Error String :=
  if value.isEmpty then .ok value
  else .ok ((parseWithOverride { dummyUrl with fragment := some "" } value .fragment).fragment.getD "")

end Urllib.UrlPattern
