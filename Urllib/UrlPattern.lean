import Urllib.UrlPattern.ConstructorString
import Urllib.SearchParams

namespace Urllib

open Urllib.Url

/-- The options of the URLPattern constructor. -/
structure UrlPatternOptions where
  /-- Whether the matching of the pathname, the search, and the hash ignores case. -/
  ignoreCase : Bool := false
  deriving DecidableEq, Repr

/-- A pattern for the URLs of a site, made of one compiled pattern per component. -/
structure UrlPattern where
  /-- The protocol component. -/
  protocol : UrlPattern.Component
  /-- The username component. -/
  username : UrlPattern.Component
  /-- The password component. -/
  password : UrlPattern.Component
  /-- The hostname component. -/
  hostname : UrlPattern.Component
  /-- The port component. -/
  port : UrlPattern.Component
  /-- The pathname component. -/
  pathname : UrlPattern.Component
  /-- The search component. -/
  search : UrlPattern.Component
  /-- The hash component. -/
  hash : UrlPattern.Component

namespace UrlPattern

/-- An input of the constructor or of a match: a string, a URL, or a dictionary of components. -/
inductive Input where
  /-- A string: a constructor string for the constructor, a URL for a match. -/
  | string (text : String)
  /-- A parsed URL, which a match serializes. -/
  | url (url : Url)
  /-- A dictionary of components. -/
  | init (init : Init)
  deriving DecidableEq, Repr

/-- The result of matching one component: the input and the groups with their values. -/
structure ComponentResult where
  /-- The input of the component. -/
  input : String
  /-- The group names and what they matched, none for a group that took no part. -/
  groups : List (String × Option String)
  deriving DecidableEq, Repr

/-- The result of a match. -/
structure Result where
  /-- The inputs of the match. -/
  inputs : List Input
  /-- The protocol result. -/
  protocol : ComponentResult
  /-- The username result. -/
  username : ComponentResult
  /-- The password result. -/
  password : ComponentResult
  /-- The hostname result. -/
  hostname : ComponentResult
  /-- The port result. -/
  port : ComponentResult
  /-- The pathname result. -/
  pathname : ComponentResult
  /-- The search result. -/
  search : ComponentResult
  /-- The hash result. -/
  hash : ComponentResult
  deriving DecidableEq, Repr

/-- The component of a pattern. -/
def get (pattern : UrlPattern) : ComponentName → Component
  | .protocol => pattern.protocol
  | .username => pattern.username
  | .password => pattern.password
  | .hostname => pattern.hostname
  | .port => pattern.port
  | .pathname => pattern.pathname
  | .search => pattern.search
  | .hash => pattern.hash

/-- Whether a hostname pattern is an IPv6 address: it starts with a bracket, possibly after a brace or a backslash. -/
def isIpv6Pattern (input : String) : Bool :=
  match input.toList with
  | first :: second :: _ => first == '[' || (first == '{' && second == '[') || (first == '\\' && second == '[')
  | _ => false

/-- Creates a pattern from a constructor string or a dictionary. -/
def create (input : Input) (baseUrl : Option String := none) (options : UrlPatternOptions := {}) :
    Except Error UrlPattern := do
  let init ←
    match input with
    | .string text =>
      let parsed ← parseConstructorString text
      if baseUrl.isNone && parsed.protocol.isNone then throw .input
      pure (match baseUrl with | some b => { parsed with baseUrl := some b } | none => parsed)
    | .url _ => throw .input
    | .init i => if baseUrl.isSome then throw .input else pure i
  let processed ← processInit init .pattern
  let value (name : ComponentName) : String := (processed.get name).getD "*"
  let protocolValue := value .protocol
  let portValue :=
    match defaultPort? protocolValue with
    | some d => if value .port == toString d then "" else value .port
    | none => value .port
  let protocol ← compileComponent protocolValue canonicalizeProtocol Options.default
  let username ← compileComponent (value .username) canonicalizeUsername Options.default
  let password ← compileComponent (value .password) canonicalizePassword Options.default
  let hostname ←
    if isIpv6Pattern (value .hostname) then
      compileComponent (value .hostname) canonicalizeIpv6Hostname Options.hostname
    else compileComponent (value .hostname) canonicalizeHostname Options.hostname
  let port ← compileComponent portValue (canonicalizePort · none) Options.default
  let pathname ←
    if protocol.matchesSpecialScheme then
      compileComponent (value .pathname) canonicalizePathname { Options.pathname with ignoreCase := options.ignoreCase }
    else compileComponent (value .pathname) canonicalizeOpaquePathname { Options.default with ignoreCase := options.ignoreCase }
  let search ← compileComponent (value .search) canonicalizeSearch { Options.default with ignoreCase := options.ignoreCase }
  let hash ← compileComponent (value .hash) canonicalizeHash { Options.default with ignoreCase := options.ignoreCase }
  return { protocol, username, password, hostname, port, pathname, search, hash }

/-- Whether any component of the pattern has a custom regular expression group. -/
def hasRegexpGroups (pattern : UrlPattern) : Bool :=
  ComponentName.all.any fun name => (pattern.get name).hasRegexpGroups

/-- The result of a component: the input and the groups. -/
def componentResult (component : Component) (input : String) (captures : List (Option String)) : ComponentResult :=
  { input := input, groups := component.groupNames.zipIdx.map fun (name, i) => (name, (captures[i]?).getD none) }

/-- Matches the pattern against an input; a failure to process the input is a mismatch, not an error. -/
def exec (pattern : UrlPattern) (input : Input) (baseUrl : Option String := none) : Except Error (Option Result) := do
  let mut inputs : List Input := []
  let values : Option Init ←
    match input with
    | .url u =>
      inputs := [.string u.serialize]
      pure (some { protocol := some u.scheme, username := some u.username, password := some u.password,
                   hostname := some (match u.host with | some h => h.serialize | none => ""),
                   port := some u.portText, pathname := some (serializePath u.path),
                   search := some (u.query.getD ""), hash := some (u.fragment.getD "") })
    | .init i =>
      inputs := [.init i]
      if baseUrl.isSome then throw .input
      match processInit i .url {} with
      | .ok processed => pure (some processed)
      | .error _ => pure none
    | .string text =>
      inputs := [.string text]
      let base : Except ParseError (Option Url) :=
        match baseUrl with
        | none => .ok none
        | some b => (parse b none).map some
      match base with
      | .error _ => pure none
      | .ok baseParsed =>
        if let some b := baseUrl then inputs := inputs ++ [.string b]
        match parse text baseParsed with
        | .error _ => pure none
        | .ok u =>
          pure (some { protocol := some u.scheme, username := some u.username, password := some u.password,
                       hostname := some (match u.host with | some h => h.serialize | none => ""),
                       port := some u.portText, pathname := some (serializePath u.path),
                       search := some (u.query.getD ""), hash := some (u.fragment.getD "") })
  match values with
  | none => return none
  | some v =>
    let component (name : ComponentName) : String := (v.get name).getD ""
    let run (name : ComponentName) := (pattern.get name).regexp.exec (component name)
    match run .protocol, run .username, run .password, run .hostname, run .port, run .pathname, run .search, run .hash with
    | some a, some b, some c, some d, some e, some f, some g, some h =>
      let make (name : ComponentName) (captures : List (Option String)) :=
        componentResult (pattern.get name) (component name) captures
      return some { inputs := inputs, protocol := make .protocol a, username := make .username b,
                    password := make .password c, hostname := make .hostname d, port := make .port e,
                    pathname := make .pathname f, search := make .search g, hash := make .hash h }
    | _, _, _, _, _, _, _, _ => return none

/-- Whether the pattern matches the input. -/
def test (pattern : UrlPattern) (input : Input) (baseUrl : Option String := none) : Except Error Bool :=
  (pattern.exec input baseUrl).map Option.isSome

/-- Generates the text of a component by filling its groups with the given values; fails when a required group has no value, when a fixed text has a modifier, or when a value for a segment wildcard contains the delimiter. -/
def generate (pattern : UrlPattern) (component : ComponentName) (groups : List (String × String)) : Except Error String := do
  let c := pattern.get component
  let mut out := ""
  for part in c.parts do
    if part.type == .fixedText then
      if part.modifier != .none then throw .input
      out := out ++ part.value
    else
      match groups.lookup part.name with
      | none =>
        if part.modifier != .optional && part.modifier != .zeroOrMore then throw .input
      | some value =>
        if part.type == .segmentWildcard && !c.options.delimiter.isEmpty &&
            value.toList.any (fun ch => String.singleton ch == c.options.delimiter) then
          throw .input
        let encoded ← c.encode value
        out := out ++ part.leading ++ encoded ++ part.trailing
  return out

/-- Compares two strings by UTF-16 code units: -1, 0, or 1. -/
def compareText (a b : String) : Int :=
  let rec go : List Nat → List Nat → Int
    | [], [] => 0
    | [], _ => -1
    | _, [] => 1
    | x :: xs, y :: ys => if x < y then -1 else if y < x then 1 else go xs ys
  go (SearchParams.utf16Units a) (SearchParams.utf16Units b)

/-- A fixed text with a modifier counts as a regular expression when parts are compared. -/
def effectiveType (part : Part) : PartType :=
  if part.type == .fixedText && part.modifier != .none then .regexp else part.type

/-- Joins neighbouring fixed texts without modifier. -/
def mergeFixedParts (parts : List Part) : List Part :=
  (parts.foldl (fun (acc : List Part) p =>
    match acc with
    | last :: rest =>
      if last.type == .fixedText && last.modifier == .none && p.type == .fixedText && p.modifier == .none then
        { last with value := last.value ++ p.value } :: rest
      else p :: acc
    | [] => [p]) []).reverse

/-- Compares the specificity of two parts: 1 when the left part is more specific, -1 when the right part is. -/
def compareParts (left right : Part) : Int :=
  let lk := effectiveType left
  let rk := effectiveType right
  if lk == .fixedText && rk == .fixedText then compareText left.value right.value
  else if lk == .fixedText then 1
  else if rk == .fixedText then -1
  else
    let affixes := compareText (left.leading ++ left.trailing) (right.leading ++ right.trailing)
    if affixes != 0 then affixes
    else if left.modifier == right.modifier then
      if lk == .regexp && rk == .regexp then
        let lv := if left.type == .fixedText then escapeRegexp left.value else left.value
        let rv := if right.type == .fixedText then escapeRegexp right.value else right.value
        compareText lv rv
      else if lk == .regexp then 1
      else if rk == .regexp then -1
      else if lk == .segmentWildcard && rk != .segmentWildcard then 1
      else if rk == .segmentWildcard && lk != .segmentWildcard then -1
      else 0
    else if left.modifier == .none then 1
    else if right.modifier == .none then -1
    else if left.modifier == .oneOrMore then 1
    else if right.modifier == .oneOrMore then -1
    else if left.modifier == .optional then 1
    else if right.modifier == .optional then -1
    else 0

/-- Compares two part lists part by part; a longer list is more specific. -/
def compareLists : List Part → List Part → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | l :: ls, r :: rs =>
    let c := compareParts l r
    if c != 0 then c else compareLists ls rs

/-- Compares the specificity of one component of two patterns: 1 when the left one is more specific, -1 when the right one is, 0 when they are equal. -/
def compareComponent (component : ComponentName) (left right : UrlPattern) : Int :=
  compareLists (mergeFixedParts (left.get component).parts) (mergeFixedParts (right.get component).parts)

end UrlPattern

end Urllib
