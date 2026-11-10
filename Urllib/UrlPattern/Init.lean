import Urllib.UrlPattern.Canonicalize

namespace Urllib.UrlPattern

open Urllib.Url

/-- The components of a URL pattern. -/
inductive ComponentName where
  /-- The protocol. -/
  | protocol
  /-- The username. -/
  | username
  /-- The password. -/
  | password
  /-- The hostname. -/
  | hostname
  /-- The port. -/
  | port
  /-- The pathname. -/
  | pathname
  /-- The search. -/
  | search
  /-- The hash. -/
  | hash
  deriving DecidableEq, Repr

/-- The components in the order of the URL syntax. -/
def ComponentName.all : List ComponentName :=
  [.protocol, .username, .password, .hostname, .port, .pathname, .search, .hash]

/-- The `URLPatternInit` dictionary: every member is optional. -/
structure Init where
  /-- The protocol. -/
  protocol : Option String := none
  /-- The username. -/
  username : Option String := none
  /-- The password. -/
  password : Option String := none
  /-- The hostname. -/
  hostname : Option String := none
  /-- The port. -/
  port : Option String := none
  /-- The pathname. -/
  pathname : Option String := none
  /-- The search. -/
  search : Option String := none
  /-- The hash. -/
  hash : Option String := none
  /-- The base URL. -/
  baseUrl : Option String := none
  deriving DecidableEq, Repr

/-- A member of the dictionary. -/
def Init.get (init : Init) : ComponentName → Option String
  | .protocol => init.protocol
  | .username => init.username
  | .password => init.password
  | .hostname => init.hostname
  | .port => init.port
  | .pathname => init.pathname
  | .search => init.search
  | .hash => init.hash

/-- Sets a member of the dictionary. -/
def Init.set (init : Init) : ComponentName → Option String → Init
  | .protocol, v => { init with protocol := v }
  | .username, v => { init with username := v }
  | .password, v => { init with password := v }
  | .hostname, v => { init with hostname := v }
  | .port, v => { init with port := v }
  | .pathname, v => { init with pathname := v }
  | .search, v => { init with search := v }
  | .hash, v => { init with hash := v }

/-- Whether processing treats the strings as patterns or as URL components. -/
inductive InitType where
  /-- The strings are pattern strings and are left as they are. -/
  | pattern
  /-- The strings are URL components and are canonicalized. -/
  | url
  deriving DecidableEq, Repr

/-- Processes a string that comes from a base URL: in a pattern it has to be escaped. -/
def processBaseUrlString (input : String) (type : InitType) : String :=
  if type == .pattern then escapePattern input else input

/-- Whether a pathname is absolute; a pattern also counts an escaped or grouped slash. -/
def isAbsolutePathname (input : String) (type : InitType) : Bool :=
  match input.toList with
  | [] => false
  | first :: rest =>
    if first == '/' then true
    else if type == .url then false
    else
      match rest with
      | second :: _ => (first == '\\' && second == '/') || (first == '{' && second == '/')
      | [] => false

/-- Removes one trailing colon. -/
def stripTrailingColon (value : String) : String :=
  if value.endsWith ":" then String.ofList value.toList.dropLast else value

/-- Removes one leading character if it is the given one. -/
def stripLeading (c : Char) (value : String) : String :=
  match value.toList with
  | first :: rest => if first == c then String.ofList rest else value
  | [] => value

/-- The position of the last slash in a string, counted in code points. -/
def lastSlashIndex (text : String) : Option Nat :=
  let chars := text.toList
  (chars.zipIdx.filter fun (c, _) => c == '/').getLast?.map (·.2)

/-- Processes a URLPatternInit: fills the components from the base URL and canonicalizes them when `type` is `url`. -/
def processInit (init : Init) (type : InitType) (initial : Init := {}) : Except Error Init := do
  let mut result : Init := { initial with baseUrl := none }
  let mut baseUrl : Option Url := none
  if let some base := init.baseUrl then
    let b ← match parse base none with
      | .error _ => throw .input
      | .ok u => pure u
    baseUrl := some b
    if init.protocol.isNone then result := { result with protocol := some (processBaseUrlString b.scheme type) }
    if type != .pattern && init.protocol.isNone && init.hostname.isNone && init.port.isNone && init.username.isNone then
      result := { result with username := some (processBaseUrlString b.username type) }
    if type != .pattern && init.protocol.isNone && init.hostname.isNone && init.port.isNone && init.username.isNone &&
        init.password.isNone then
      result := { result with password := some (processBaseUrlString b.password type) }
    if init.protocol.isNone && init.hostname.isNone then
      let baseHost := match b.host with | some h => h.serialize | none => ""
      result := { result with hostname := some (processBaseUrlString baseHost type) }
    if init.protocol.isNone && init.hostname.isNone && init.port.isNone then
      result := { result with port := some (match b.port with | none => "" | some p => toString p) }
    if init.protocol.isNone && init.hostname.isNone && init.port.isNone && init.pathname.isNone then
      result := { result with pathname := some (processBaseUrlString (serializePath b.path) type) }
    if init.protocol.isNone && init.hostname.isNone && init.port.isNone && init.pathname.isNone && init.search.isNone then
      result := { result with search := some (processBaseUrlString (b.query.getD "") type) }
    if init.protocol.isNone && init.hostname.isNone && init.port.isNone && init.pathname.isNone &&
        init.search.isNone && init.hash.isNone then
      result := { result with hash := some (processBaseUrlString (b.fragment.getD "") type) }
  if let some value := init.protocol then
    let stripped := stripTrailingColon value
    result := { result with protocol := some (← if type == .pattern then pure stripped else canonicalizeProtocol stripped) }
  if let some value := init.username then
    result := { result with username := some (← if type == .pattern then pure value else canonicalizeUsername value) }
  if let some value := init.password then
    result := { result with password := some (← if type == .pattern then pure value else canonicalizePassword value) }
  if let some value := init.hostname then
    result := { result with hostname := some (← if type == .pattern then pure value else canonicalizeHostname value) }
  let protocolString := result.protocol.getD ""
  if let some value := init.port then
    result := { result with port := some (← if type == .pattern then pure value else canonicalizePort value (some protocolString)) }
  if let some value := init.pathname then
    let mut pathname := value
    if let some b := baseUrl then
      if !b.hasOpaquePath && !isAbsolutePathname pathname type then
        let basePath := processBaseUrlString (serializePath b.path) type
        match lastSlashIndex basePath with
        | some slash => pathname := String.ofList (basePath.toList.take (slash + 1)) ++ pathname
        | none => pure ()
    result := { result with pathname := some (← if type == .pattern then pure pathname
      else if isSpecialScheme protocolString || protocolString.isEmpty then canonicalizePathname pathname
      else canonicalizeOpaquePathname pathname) }
  if let some value := init.search then
    let stripped := stripLeading '?' value
    result := { result with search := some (← if type == .pattern then pure stripped else canonicalizeSearch stripped) }
  if let some value := init.hash then
    let stripped := stripLeading '#' value
    result := { result with hash := some (← if type == .pattern then pure stripped else canonicalizeHash stripped) }
  return result

end Urllib.UrlPattern
