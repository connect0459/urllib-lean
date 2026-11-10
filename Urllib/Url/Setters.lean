import Urllib.Url.Parser
import Urllib.SearchParams

namespace Urllib.Url

open Parser

/-- Removes ASCII tabs and newlines, the only cleaning that a setter applies to its input. -/
def removeTabsAndNewlines (input : String) : List Char :=
  input.toList.filter fun c => !(c == Char.ofNat 9 || c == Char.ofNat 10 || c == Char.ofNat 13)

/-- Runs the basic URL parser on `input` with `url` as the URL and `state` as the state override; a failure is reported, and the changes made before it are lost. -/
def parseWithOverrideStrict (url : Url) (input : String) (state : State) : Except ParseError Url :=
  let chars := (removeTabsAndNewlines input).toArray
  run chars none (some state) false (16 * (chars.size + 8))
    { state := state, url := url, buffer := "", atSignSeen := false,
      insideBrackets := false, passwordTokenSeen := false } 0

/-- Runs the basic URL parser on `input` with `url` as the URL and `state` as the state override, and returns the modified URL; a failure leaves the changes made before it. -/
def parseWithOverride (url : Url) (input : String) (state : State) : Url :=
  let chars := (removeTabsAndNewlines input).toArray
  match run chars none (some state) true (16 * (chars.size + 8))
      { state := state, url := url, buffer := "", atSignSeen := false,
        insideBrackets := false, passwordTokenSeen := false } 0 with
  | .ok updated => updated
  | .error _ => url

/-- The `href` setter: parses the value as a new URL. -/
def setHref (value : String) : Except ParseError Url :=
  parse value none

/-- The `protocol` setter; an invalid or refused scheme leaves the URL as it is. -/
def setProtocol (url : Url) (value : String) : Url :=
  parseWithOverride url (value ++ ":") .schemeStart

/-- The `username` setter. -/
def setUsername (url : Url) (value : String) : Url :=
  if url.cannotHaveCredentials then url
  else { url with username := PercentEncoding.utf8PercentEncode .userinfo value }

/-- The `password` setter. -/
def setPassword (url : Url) (value : String) : Url :=
  if url.cannotHaveCredentials then url
  else { url with password := PercentEncoding.utf8PercentEncode .userinfo value }

/-- The `host` setter: a value without a port leaves the port as it is. -/
def setHost (url : Url) (value : String) : Url :=
  if url.hasOpaquePath then url else parseWithOverride url value .host

/-- The `hostname` setter. -/
def setHostname (url : Url) (value : String) : Url :=
  if url.hasOpaquePath then url else parseWithOverride url value .hostname

/-- The `port` setter: the empty string removes the port. -/
def setPort (url : Url) (value : String) : Url :=
  if url.cannotHaveCredentials then url
  else if value.isEmpty then { url with port := none }
  else parseWithOverride url value .port

/-- The `pathname` setter. -/
def setPathname (url : Url) (value : String) : Url :=
  if url.hasOpaquePath then url
  else parseWithOverride { url with path := .list [] } value .pathStart

/-- The `search` setter: the empty string removes the query, and one leading question mark is dropped. -/
def setSearch (url : Url) (value : String) : Url :=
  if value.isEmpty then { url with query := none }
  else
    let input := if value.startsWith "?" then (value.drop 1).toString else value
    parseWithOverride { url with query := some "" } input .query

/-- The `hash` setter: the empty string removes the fragment, and one leading number sign is dropped. -/
def setHash (url : Url) (value : String) : Url :=
  if value.isEmpty then { url with fragment := none }
  else
    let input := if value.startsWith "#" then (value.drop 1).toString else value
    parseWithOverride { url with fragment := some "" } input .fragment

/-- `URL.canParse`: whether the input parses, against the base when one is given. -/
def canParse (input : String) (base : Option String := none) : Bool :=
  match base with
  | none => (parse input none).isOk
  | some b =>
    match parse b none with
    | .ok baseUrl => (parse input (some baseUrl)).isOk
    | .error _ => false

/-- Resolves a reference against the URL. -/
def join (url : Url) (reference : String) : Except ParseError Url :=
  parse reference (some url)

/-- The query parsed as `application/x-www-form-urlencoded`, as `searchParams` of the URL API starts out. -/
def searchParams (url : Url) : SearchParams :=
  { pairs := FormUrlencoded.parse (url.query.getD "") }

/-- The update steps of a `URLSearchParams` bound to a URL: the serialized list becomes the query, and the empty serialization removes it. -/
def withSearchParams (url : Url) (params : SearchParams) : Url :=
  let serialized := params.toString
  { url with query := if serialized.isEmpty then none else some serialized }

/-- Applies an operation on the search params of the URL and runs the update steps on the result. -/
def updateSearchParams (url : Url) (operation : SearchParams → SearchParams) : Url :=
  url.withSearchParams (operation url.searchParams)

end Urllib.Url
