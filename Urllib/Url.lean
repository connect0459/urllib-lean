import Urllib.Host

namespace Urllib

/-- The path of a URL: an opaque string, or a list of segments. -/
inductive UrlPath where
  /-- The opaque path of a URL such as `mailto:a@b`. -/
  | opaque (text : String)
  /-- A list of path segments. -/
  | list (segments : List String)
  deriving DecidableEq, Repr

/-- A URL record of the URL Standard. -/
structure Url where
  /-- The scheme, in lowercase and without the colon. -/
  scheme : String
  /-- The username, percent-encoded. -/
  username : String
  /-- The password, percent-encoded. -/
  password : String
  /-- The host, if any. -/
  host : Option Host
  /-- The port, if it is not the default of the scheme. -/
  port : Option Nat
  /-- The path. -/
  path : UrlPath
  /-- The query, without the question mark. -/
  query : Option String
  /-- The fragment, without the number sign. -/
  fragment : Option String
  deriving DecidableEq, Repr

namespace Url

/-- The schemes that the URL Standard calls special. -/
def specialSchemes : List String := ["ftp", "file", "http", "https", "ws", "wss"]

/-- The default port of a special scheme; `file` has none. -/
def defaultPort? (scheme : String) : Option Nat :=
  match scheme with
  | "ftp" => some 21
  | "http" => some 80
  | "https" => some 443
  | "ws" => some 80
  | "wss" => some 443
  | _ => none

/-- Whether the scheme is special. -/
def isSpecialScheme (scheme : String) : Bool :=
  specialSchemes.contains scheme

/-- Whether the URL has a special scheme. -/
def isSpecial (url : Url) : Bool :=
  isSpecialScheme url.scheme

/-- Whether the URL has a username or a password. -/
def hasCredentials (url : Url) : Bool :=
  !url.username.isEmpty || !url.password.isEmpty

/-- Whether the URL cannot have a username, a password, or a port: it has no host, an empty host, or the file scheme. -/
def cannotHaveCredentials (url : Url) : Bool :=
  match url.host with
  | none | some .empty => true
  | some _ => url.scheme == "file"

/-- The segments of a list path; an opaque path has none. -/
def pathSegments (url : Url) : List String :=
  match url.path with
  | .list segments => segments
  | .opaque _ => []

/-- Whether the URL has an opaque path. -/
def hasOpaquePath (url : Url) : Bool :=
  match url.path with
  | .opaque _ => true
  | .list _ => false

/-- The serialization of the path. -/
def serializePath (path : UrlPath) : String :=
  match path with
  | .opaque text => text
  | .list segments => String.join (segments.map fun s => "/" ++ s)

/-- The serialization of the host and the port: `hostname:port` without a port when it is absent. -/
def serializeAuthorityHost (url : Url) : String :=
  match url.host with
  | none => ""
  | some host => host.serialize ++ (url.port.map fun p => ":" ++ toString p).getD ""

/-- The userinfo with its trailing at sign, or the empty string without credentials. -/
def serializeUserinfo (url : Url) : String :=
  if url.username.isEmpty && url.password.isEmpty then ""
  else url.username ++ (if url.password.isEmpty then "" else ":" ++ url.password) ++ "@"

/-- The URL serializer of the URL Standard, `href` of the URL API. -/
def serialize (url : Url) : String :=
  let authority :=
    match url.host with
    | some _ => "//" ++ serializeUserinfo url ++ serializeAuthorityHost url
    | none =>
      match url.path with
      | .list ("" :: _ :: _) => "/."
      | _ => ""
  url.scheme ++ ":" ++ authority ++ serializePath url.path ++
    (url.query.map fun q => "?" ++ q).getD "" ++ (url.fragment.map fun f => "#" ++ f).getD ""

/-- `protocol` of the URL API. -/
def protocol (url : Url) : String :=
  url.scheme ++ ":"

/-- `host` of the URL API: the host with the port. -/
def hostWithPort (url : Url) : String :=
  serializeAuthorityHost url

/-- `hostname` of the URL API. -/
def hostname (url : Url) : String :=
  match url.host with
  | none => ""
  | some host => host.serialize

/-- `port` of the URL API. -/
def portText (url : Url) : String :=
  (url.port.map toString).getD ""

/-- `pathname` of the URL API. -/
def pathname (url : Url) : String :=
  serializePath url.path

/-- `search` of the URL API. -/
def search (url : Url) : String :=
  match url.query with
  | none | some "" => ""
  | some q => "?" ++ q

/-- `hash` of the URL API. -/
def hash (url : Url) : String :=
  match url.fragment with
  | none | some "" => ""
  | some f => "#" ++ f

end Url

end Urllib
