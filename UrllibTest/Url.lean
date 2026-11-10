import UrllibTest.Support
import UrllibTest.Url.Vectors
import Urllib.Url.Parser

namespace UrllibTest.Url

open Urllib

structure Vector where
  input : String
  base : Option String
  failure : Bool
  href : String
  protocol : String
  username : String
  password : String
  host : String
  hostname : String
  port : String
  pathname : String
  search : String
  hash : String
  origin : Option String

def optionalField (field : String) : Option String :=
  if field.startsWith "S" then some (field.drop 1).toString else none

def parseVector (record : String) : Option Vector :=
  match record.splitOn (String.singleton fieldSeparator) with
  | [input, base, outcome, href, protocol, username, password, host, hostname, port, pathname, search, hash, origin] =>
    some { input, base := optionalField base, failure := outcome == "F", href, protocol, username, password, host,
           hostname, port, pathname, search, hash, origin := optionalField origin }
  | _ => none

def allVectors : List Vector :=
  (vectors.splitOn (String.singleton recordSeparator)).filterMap parseVector

def parseWithBase (input : String) (base : Option String) : Except Url.ParseError Url :=
  match base with
  | none => Url.parse input none
  | some b => do
    let baseUrl ← Url.parse b none
    Url.parse input (some baseUrl)

def mismatches (v : Vector) : List String :=
  match parseWithBase v.input v.base with
  | .error _ => if v.failure then [] else [s!"unexpected failure: {repr v.input} {repr v.base}"]
  | .ok url =>
    if v.failure then [s!"missing failure: {repr v.input} {repr v.base} gave {url.serialize}"]
    else
      let fields : List (String × String × String) := [
        ("href", url.serialize, v.href), ("protocol", url.protocol, v.protocol),
        ("username", url.username, v.username), ("password", url.password, v.password),
        ("host", url.hostWithPort, v.host), ("hostname", url.hostname, v.hostname),
        ("port", url.portText, v.port), ("pathname", url.pathname, v.pathname),
        ("search", url.search, v.search), ("hash", url.hash, v.hash)]
      let originField : List (String × String × String) :=
        match v.origin with
        | some expected => [("origin", url.origin, expected)]
        | none => []
      (fields ++ originField).filterMap fun (name, actual, expected) =>
        if actual == expected then none
        else some s!"{name} of {repr v.input} {repr v.base}: {repr actual} instead of {repr expected}"

def failures : List String := allVectors.flatMap mismatches

/-- info: [] -/
#guard_msgs in
#eval failures.take 20

end UrllibTest.Url
