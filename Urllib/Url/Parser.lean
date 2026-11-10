import Urllib.Url

namespace Urllib.Url

/-- Reasons why the URL parser fails. -/
inductive ParseError where
  /-- The input has no scheme and there is no base URL, or the base has an opaque path and the input is not a fragment. -/
  | missingBase
  /-- Credentials are present but the host is empty. -/
  | hostMissing
  /-- The host of a special URL is empty, or a port follows an empty host. -/
  | emptyHost
  /-- The port is not a number in the range 0 to 65535, or is followed by an unexpected code point. -/
  | invalidPort
  /-- The host parser failed. -/
  | host (error : Host.Error)
  /-- The state machine ran out of steps, which a well-formed run never does. -/
  | fuelExhausted
  deriving DecidableEq, Repr

namespace Parser

/-- The states of the basic URL parser. -/
inductive State where
  /-- Scheme start state. -/
  | schemeStart
  /-- Scheme state. -/
  | scheme
  /-- No scheme state. -/
  | noScheme
  /-- Special relative or authority state. -/
  | specialRelativeOrAuthority
  /-- Path or authority state. -/
  | pathOrAuthority
  /-- Relative state. -/
  | relative
  /-- Relative slash state. -/
  | relativeSlash
  /-- Special authority slashes state. -/
  | specialAuthoritySlashes
  /-- Special authority ignore slashes state. -/
  | specialAuthorityIgnoreSlashes
  /-- Authority state. -/
  | authority
  /-- Host state. -/
  | host
  /-- Hostname state, the host state as a state override of the hostname setter. -/
  | hostname
  /-- Port state. -/
  | port
  /-- File state. -/
  | file
  /-- File slash state. -/
  | fileSlash
  /-- File host state. -/
  | fileHost
  /-- Path start state. -/
  | pathStart
  /-- Path state. -/
  | path
  /-- Opaque path state. -/
  | opaquePath
  /-- Query state. -/
  | query
  /-- Fragment state. -/
  | fragment
  deriving DecidableEq, Repr

/-- The mutable part of the state machine. -/
structure Machine where
  /-- The current state. -/
  state : State
  /-- The URL under construction. -/
  url : Url
  /-- The buffer of the URL parser. -/
  buffer : String
  /-- The at sign flag. -/
  atSignSeen : Bool
  /-- The inside brackets flag. -/
  insideBrackets : Bool
  /-- The password token seen flag. -/
  passwordTokenSeen : Bool

/-- The outcome of one step: continue at a pointer, finish, or fail. -/
inductive Step where
  /-- Continue with the machine at the given pointer. -/
  | next (machine : Machine) (pointer : Nat)
  /-- Fail. -/
  | fail (error : ParseError)
  /-- Stop and return the URL as it is: the `return` of a state override. -/
  | done (machine : Machine)

/-- The segments of a list path; an opaque path has none. -/
def pathSegments (path : UrlPath) : List String :=
  match path with
  | .list segments => segments
  | .opaque _ => []

/-- Whether two code points form a Windows drive letter: an ASCII letter and a colon or a vertical bar. -/
def isWindowsDriveLetter (chars : List Char) : Bool :=
  match chars with
  | [letter, mark] => letter.isAlpha && (mark == ':' || mark == '|')
  | _ => false

/-- Whether the code points form a Windows drive letter whose second code point is a colon. -/
def isNormalizedWindowsDriveLetter (chars : List Char) : Bool :=
  match chars with
  | [letter, mark] => letter.isAlpha && mark == ':'
  | _ => false

/-- Whether the code points start with a Windows drive letter that is followed by nothing or by a delimiter. -/
def startsWithWindowsDriveLetter (chars : List Char) : Bool :=
  match chars with
  | letter :: mark :: rest =>
    isWindowsDriveLetter [letter, mark] &&
      match rest with
      | [] => true
      | c :: _ => c == '/' || c == '\\' || c == '?' || c == '#'
  | _ => false

/-- Removes the last segment of a path, except for the drive letter of a file URL. -/
def shortenPath (scheme : String) (segments : List String) : List String :=
  match segments with
  | [only] => if scheme == "file" && isNormalizedWindowsDriveLetter only.toList then segments else []
  | _ => segments.dropLast

/-- Whether a path segment is a double-dot segment. -/
def isDoubleDotSegment (segment : String) : Bool :=
  [String.append "." ".", ".%2e", "%2e.", "%2e%2e"].contains (segment.map Char.toLower)

/-- Whether a path segment is a single-dot segment. -/
def isSingleDotSegment (segment : String) : Bool :=
  [".", "%2e"].contains (segment.map Char.toLower)

/-- Whether the code point ends an authority, a host, a port, or a path segment of the URL. -/
def endsComponent (special : Bool) (c : Option Char) : Bool :=
  match c with
  | none => true
  | some ch => ch == '/' || ch == '?' || ch == '#' || (special && ch == '\\')

/-- The URL under construction at the start of a parse. -/
def emptyUrl : Url :=
  { scheme := "", username := "", password := "", host := none, port := none,
    path := .list [], query := none, fragment := none }

/-- The data a step can read: the input, the base URL, the machine, and the pointer. -/
structure Env where
  /-- The preprocessed input. -/
  input : Array Char
  /-- The base URL. -/
  base : Option Url
  /-- The machine. -/
  m : Machine
  /-- The pointer. -/
  pointer : Nat
  /-- The state override, if the parse is run by a setter. -/
  override : Option State

namespace Env

/-- The code point at the pointer, or none at the end of the input. -/
def c (e : Env) : Option Char := e.input[e.pointer]?

/-- The code point after the pointer. -/
def after (e : Env) : Option Char := e.input[e.pointer + 1]?

/-- The code points from the pointer on. -/
def rest (e : Env) : List Char := e.input.toList.drop e.pointer

/-- The URL under construction. -/
def url (e : Env) : Url := e.m.url

/-- Whether the URL under construction is special. -/
def special (e : Env) : Bool := e.m.url.isSpecial

/-- Continues with the next code point. -/
def next (e : Env) (m : Machine) : Step := .next m (e.pointer + 1)

/-- Processes the same code point again, which the specification writes as decreasing the pointer. -/
def stay (e : Env) (m : Machine) : Step := .next m e.pointer

/-- Skips one more code point, which the specification writes as increasing the pointer. -/
def skip (e : Env) (m : Machine) : Step := .next m (e.pointer + 2)

/-- The machine in another state. -/
def go (e : Env) (state : State) : Machine := { e.m with state := state }

/-- Fails; with a state override the URL is left as it is, because the setter then ignores the failure. -/
def fail (e : Env) (error : ParseError) : Step :=
  if e.override.isSome then .done e.m else .fail error

/-- The machine with another URL in another state. -/
def withUrl (e : Env) (url : Url) (state : State) : Machine := { e.m with url := url, state := state }

end Env

/-- Parses a host for the URL; a non-special URL gets an opaque host. -/
def parseHost (url : Url) (text : String) : Except ParseError Host :=
  (Host.parse text (!url.isSpecial)).mapError ParseError.host

/-- The query state's start: the empty query and the query state. -/
def startQuery (e : Env) (url : Url) : Step :=
  e.next { e.m with url := { url with query := some "" }, state := .query, buffer := "" }

/-- The fragment state's start: the empty fragment and the fragment state. -/
def startFragment (e : Env) (url : Url) : Step :=
  e.next { e.m with url := { url with fragment := some "" }, state := .fragment, buffer := "" }

/-- Scheme start state. -/
def schemeStart (e : Env) : Step :=
  match e.c with
  | some ch =>
    if ch.isAlpha then e.next { e.m with state := .scheme, buffer := e.m.buffer.push ch.toLower }
    else if e.override.isSome then e.fail .missingBase
    else e.stay (e.go .noScheme)
  | none => if e.override.isSome then e.fail .missingBase else e.stay (e.go .noScheme)

/-- The scheme state at a colon: with a state override, the change of scheme is refused when it would cross the special boundary or break a file URL. -/
def schemeColon (e : Env) : Step :=
  let name := e.m.buffer
  let url := e.url
  let url' := { url with scheme := name }
  let m' : Machine := { e.m with url := url', buffer := "" }
  if e.override.isSome then
    if (url.isSpecial && !isSpecialScheme name) || (!url.isSpecial && isSpecialScheme name) ||
        ((url.hasCredentials || url.port.isSome) && name == "file") ||
        (url.scheme == "file" && url.host == some .empty) then
      .done e.m
    else
      let port := if url.port.isSome && url.port == defaultPort? name then none else url.port
      .done { m' with url := { url' with port := port } }
  else if name == "file" then e.next { m' with state := .file }
  else if isSpecialScheme name then
    match e.base with
    | some b =>
      if b.scheme == name then e.next { m' with state := .specialRelativeOrAuthority }
      else e.next { m' with state := .specialAuthoritySlashes }
    | none => e.next { m' with state := .specialAuthoritySlashes }
  else if e.after == some '/' then e.skip { m' with state := .pathOrAuthority }
  else e.next { m' with url := { url' with path := .opaque "" }, state := .opaquePath }

/-- Scheme state. -/
def scheme (e : Env) : Step :=
  let restart : Step :=
    if e.override.isSome then e.fail .missingBase else .next { e.m with state := .noScheme, buffer := "" } 0
  match e.c with
  | none => restart
  | some ch =>
    if ch.isAlphanum || ch == '+' || ch == '-' || ch == '.' then
      e.next { e.m with buffer := e.m.buffer.push ch.toLower }
    else if ch == ':' then schemeColon e
    else restart

/-- No scheme state. -/
def noScheme (e : Env) : Step :=
  match e.base with
  | none => e.fail .missingBase
  | some b =>
    if b.hasOpaquePath then
      if e.c == some '#' then
        e.next (e.withUrl { e.url with scheme := b.scheme, path := b.path, query := b.query, fragment := some "" } .fragment)
      else e.fail .missingBase
    else if b.scheme != "file" then e.stay (e.go .relative)
    else e.stay (e.go .file)

/-- Relative state. -/
def relative (e : Env) : Step :=
  match e.base with
  | none => e.fail .missingBase
  | some b =>
    let url' := { e.url with scheme := b.scheme }
    if e.c == some '/' || (url'.isSpecial && e.c == some '\\') then e.next (e.withUrl url' .relativeSlash)
    else
      let copied := { url' with username := b.username, password := b.password, host := b.host, port := b.port,
                                path := b.path, query := b.query }
      if e.c == some '?' then startQuery e copied
      else if e.c == some '#' then startFragment e copied
      else if e.c.isSome then
        let shortened := UrlPath.list (shortenPath copied.scheme (pathSegments copied.path))
        e.stay (e.withUrl { copied with query := none, path := shortened } .path)
      else e.next (e.withUrl copied .relative)

/-- Relative slash state. -/
def relativeSlash (e : Env) : Step :=
  if e.special && (e.c == some '/' || e.c == some '\\') then e.next (e.go .specialAuthorityIgnoreSlashes)
  else if e.c == some '/' then e.next (e.go .authority)
  else
    match e.base with
    | none => e.fail .missingBase
    | some b =>
      e.stay (e.withUrl { e.url with username := b.username, password := b.password, host := b.host, port := b.port } .path)

/-- Authority state: collects credentials until the host starts. -/
def authority (e : Env) : Step :=
  let m := e.m
  if e.c == some '@' then
    let text := if m.atSignSeen then "%40" ++ m.buffer else m.buffer
    let (username, password, seen) := text.toList.foldl
      (fun (acc : String × String × Bool) ch =>
        if ch == ':' && !acc.2.2 then (acc.1, acc.2.1, true)
        else
          let encoded := PercentEncoding.utf8PercentEncodeCodePoint .userinfo ch
          if acc.2.2 then (acc.1, acc.2.1 ++ encoded, acc.2.2) else (acc.1 ++ encoded, acc.2.1, acc.2.2))
      (e.url.username, e.url.password, m.passwordTokenSeen)
    e.next { m with url := { e.url with username := username, password := password }, buffer := "",
                    atSignSeen := true, passwordTokenSeen := seen }
  else if endsComponent e.special e.c then
    if m.atSignSeen && m.buffer.isEmpty then e.fail .hostMissing
    else .next { m with state := .host, buffer := "" } (e.pointer - m.buffer.length)
  else
    match e.c with
    | some ch => e.next { m with buffer := m.buffer.push ch }
    | none => e.next m

/-- Host state and hostname state. -/
def host (e : Env) : Step :=
  let m := e.m
  if e.override.isSome && e.url.scheme == "file" then e.stay (e.go .fileHost)
  else if e.c == some ':' && !m.insideBrackets then
    if m.buffer.isEmpty then e.fail .emptyHost
    else if e.override == some .hostname then e.fail .emptyHost
    else
      match parseHost e.url m.buffer with
      | .error err => e.fail err
      | .ok h => e.next { m with url := { e.url with host := some h }, buffer := "", state := .port }
  else if endsComponent e.special e.c then
    if e.special && m.buffer.isEmpty then e.fail .emptyHost
    else if e.override.isSome && m.buffer.isEmpty && (e.url.hasCredentials || e.url.port.isSome) then e.fail .emptyHost
    else
      match parseHost e.url m.buffer with
      | .error err => e.fail err
      | .ok h =>
        let m' : Machine := { m with url := { e.url with host := some h }, buffer := "", state := .pathStart }
        if e.override.isSome then .done m' else e.stay m'
  else
    match e.c with
    | some ch =>
      e.next { m with insideBrackets := if ch == '[' then true else if ch == ']' then false else m.insideBrackets,
                      buffer := m.buffer.push ch }
    | none => e.next m

/-- The end of the port state: validates the digits and drops a default port. -/
def finishPort (e : Env) : Step :=
  let m := e.m
  if m.buffer.isEmpty then
    if e.override.isSome then e.fail .invalidPort else e.stay (e.go .pathStart)
  else
    let number := m.buffer.foldl (fun acc ch => acc * 10 + (ch.toNat - 48)) 0
    if 65535 < number then e.fail .invalidPort
    else
      let port := if defaultPort? e.url.scheme == some number then none else some number
      let m' : Machine := { m with url := { e.url with port := port }, buffer := "", state := .pathStart }
      if e.override.isSome then .done m' else e.stay m'

/-- Port state. -/
def port (e : Env) : Step :=
  match e.c with
  | some ch =>
    if ch.isDigit then e.next { e.m with buffer := e.m.buffer.push ch }
    else if endsComponent e.special e.c || e.override.isSome then finishPort e
    else e.fail .invalidPort
  | none => finishPort e

/-- File state. -/
def file (e : Env) : Step :=
  let url' := { e.url with scheme := "file", host := some .empty }
  if e.c == some '/' || e.c == some '\\' then e.next (e.withUrl url' .fileSlash)
  else
    match e.base with
    | some b =>
      if b.scheme == "file" then
        let copied := { url' with host := b.host, path := b.path, query := b.query }
        if e.c == some '?' then startQuery e copied
        else if e.c == some '#' then startFragment e copied
        else if e.c.isSome then
          let path :=
            if startsWithWindowsDriveLetter e.rest then UrlPath.list []
            else .list (shortenPath copied.scheme (pathSegments copied.path))
          e.stay (e.withUrl { copied with query := none, path := path } .path)
        else e.next (e.withUrl copied .file)
      else e.stay (e.withUrl url' .path)
    | none => e.stay (e.withUrl url' .path)

/-- File slash state. -/
def fileSlash (e : Env) : Step :=
  if e.c == some '/' || e.c == some '\\' then e.next (e.go .fileHost)
  else
    match e.base with
    | some b =>
      if b.scheme == "file" then
        let withHost := { e.url with host := b.host }
        let url' :=
          match b.path with
          | .list (first :: _) =>
            if !startsWithWindowsDriveLetter e.rest && isNormalizedWindowsDriveLetter first.toList then
              { withHost with path := .list (pathSegments withHost.path ++ [first]) }
            else withHost
          | _ => withHost
        e.stay (e.withUrl url' .path)
      else e.stay (e.go .path)
    | none => e.stay (e.go .path)

/-- File host state. -/
def fileHost (e : Env) : Step :=
  let m := e.m
  match e.c with
  | some ch =>
    if ch == '/' || ch == '\\' || ch == '?' || ch == '#' then fileHostEnd e
    else e.next { m with buffer := m.buffer.push ch }
  | none => fileHostEnd e
where
  fileHostEnd (e : Env) : Step :=
    let m := e.m
    if e.override.isNone && isWindowsDriveLetter m.buffer.toList then e.stay (e.go .path)
    else if m.buffer.isEmpty then
      let m' := e.withUrl { e.url with host := some .empty } .pathStart
      if e.override.isSome then .done m' else e.stay m'
    else
      match parseHost e.url m.buffer with
      | .error err => e.fail err
      | .ok h =>
        let h' := if h == .domain "localhost" then Host.empty else h
        let m' : Machine := { m with url := { e.url with host := some h' }, buffer := "", state := .pathStart }
        if e.override.isSome then .done m' else e.stay m'

/-- Path start state. -/
def pathStart (e : Env) : Step :=
  if e.special then
    if e.c == some '/' || e.c == some '\\' then e.next (e.go .path) else e.stay (e.go .path)
  else if e.override.isNone && e.c == some '?' then startQuery e e.url
  else if e.override.isNone && e.c == some '#' then startFragment e e.url
  else if e.c.isSome then
    if e.c == some '/' then e.next (e.go .path) else e.stay (e.go .path)
  else if e.override.isSome && e.url.host.isNone then
    e.next (e.withUrl { e.url with path := .list (pathSegments e.url.path ++ [""]) } e.m.state)
  else e.next e.m

/-- Path state. -/
def path (e : Env) : Step :=
  let m := e.m
  let slashEnd := e.c == some '/' || (e.special && e.c == some '\\')
  if e.c.isNone || slashEnd || (e.override.isNone && (e.c == some '?' || e.c == some '#')) then
    let segments := pathSegments e.url.path
    let segments' :=
      if isDoubleDotSegment m.buffer then
        shortenPath e.url.scheme segments ++ (if slashEnd then [] else [""])
      else if isSingleDotSegment m.buffer then
        if slashEnd then segments else segments ++ [""]
      else
        let segment :=
          if e.url.scheme == "file" && segments.isEmpty && isWindowsDriveLetter m.buffer.toList then
            String.ofList (m.buffer.toList.take 1 ++ [':'] ++ m.buffer.toList.drop 2)
          else m.buffer
        segments ++ [segment]
    let url' := { e.url with path := .list segments' }
    let m' : Machine := { m with url := url', buffer := "" }
    if e.c == some '?' then startQuery e url'
    else if e.c == some '#' then startFragment e url'
    else e.next m'
  else
    match e.c with
    | some ch => e.next { m with buffer := m.buffer ++ PercentEncoding.utf8PercentEncodeCodePoint .path ch }
    | none => e.next m

/-- Opaque path state. -/
def opaquePath (e : Env) : Step :=
  let text := match e.url.path with | .opaque t => t | .list _ => ""
  let setText (t : String) : Machine := { e.m with url := { e.url with path := .opaque t } }
  if e.c == some '?' then startQuery e e.url
  else if e.c == some '#' then startFragment e e.url
  else
    match e.c with
    | some ch =>
      if ch == ' ' && (e.after == some '?' || e.after == some '#') then e.next (setText (text ++ "%20"))
      else e.next (setText (text ++ PercentEncoding.utf8PercentEncodeCodePoint .c0Control ch))
    | none => e.next e.m

/-- Query state. -/
def query (e : Env) : Step :=
  let m := e.m
  match e.c with
  | some ch =>
    if ch == '#' && e.override.isNone then queryEnd e
    else e.next { m with buffer := m.buffer.push ch }
  | none => queryEnd e
where
  queryEnd (e : Env) : Step :=
    let set := if e.special then PercentEncoding.EncodeSet.specialQuery else .query
    let query := (e.url.query.getD "") ++ PercentEncoding.utf8PercentEncode set e.m.buffer
    let url' := { e.url with query := some query }
    if e.c == some '#' then startFragment { e with m := { e.m with buffer := "" } } url'
    else e.next { e.m with url := url', buffer := "" }

/-- Fragment state. -/
def fragment (e : Env) : Step :=
  match e.c with
  | some ch =>
    let encoded := PercentEncoding.utf8PercentEncodeCodePoint .fragment ch
    e.next { e.m with url := { e.url with fragment := some ((e.url.fragment.getD "") ++ encoded) } }
  | none => e.next e.m

/-- One step of the basic URL parser. -/
def step (e : Env) : Step :=
  match e.m.state with
  | .schemeStart => schemeStart e
  | .scheme => scheme e
  | .noScheme => noScheme e
  | .specialRelativeOrAuthority =>
    if e.c == some '/' && e.after == some '/' then e.skip (e.go .specialAuthorityIgnoreSlashes)
    else e.stay (e.go .relative)
  | .pathOrAuthority => if e.c == some '/' then e.next (e.go .authority) else e.stay (e.go .path)
  | .relative => relative e
  | .relativeSlash => relativeSlash e
  | .specialAuthoritySlashes =>
    if e.c == some '/' && e.after == some '/' then e.skip (e.go .specialAuthorityIgnoreSlashes)
    else e.stay (e.go .specialAuthorityIgnoreSlashes)
  | .specialAuthorityIgnoreSlashes =>
    if e.c == some '/' || e.c == some '\\' then e.next e.m else e.stay (e.go .authority)
  | .authority => authority e
  | .host | .hostname => host e
  | .port => port e
  | .file => file e
  | .fileSlash => fileSlash e
  | .fileHost => fileHost e
  | .pathStart => pathStart e
  | .path => path e
  | .opaquePath => opaquePath e
  | .query => query e
  | .fragment => fragment e

/-- Runs the state machine; `fuel` bounds the number of steps. -/
def run (input : Array Char) (base : Option Url) (override : Option State) : Nat → Machine → Nat → Except ParseError Url
  | 0, _, _ => .error .fuelExhausted
  | fuel + 1, m, pointer =>
    if input.size < pointer then .ok m.url
    else
      match step { input := input, base := base, m := m, pointer := pointer, override := override } with
      | .next m' pointer' => run input base override fuel m' pointer'
      | .fail err => .error err
      | .done m' => .ok m'.url

end Parser

open Parser

/-- Whether the code point is a C0 control or a space. -/
def isC0ControlOrSpace (c : Char) : Bool := c.toNat ≤ 0x20

/-- Input preprocessing: trims leading and trailing C0 controls and spaces, then removes tabs and newlines. -/
def preprocess (input : String) : List Char :=
  let trimmed := ((input.toList.dropWhile isC0ControlOrSpace).reverse.dropWhile isC0ControlOrSpace).reverse
  trimmed.filter fun c => !(c == Char.ofNat 9 || c == Char.ofNat 10 || c == Char.ofNat 13)

/-- The basic URL parser of the URL Standard without a state override. -/
def parse (input : String) (base : Option Url := none) : Except ParseError Url :=
  let chars := (preprocess input).toArray
  run chars base none (16 * (chars.size + 8))
    { state := .schemeStart, url := emptyUrl, buffer := "", atSignSeen := false,
      insideBrackets := false, passwordTokenSeen := false } 0

/-- `origin` of the URL API: the serialized origin, `null` for an opaque origin. -/
def origin (url : Url) : String :=
  if ["ftp", "http", "https", "ws", "wss"].contains url.scheme then
    url.scheme ++ "://" ++ url.hostWithPort
  else if url.scheme == "blob" then
    match parse (serializePath url.path) with
    | .ok inner => if inner.scheme == "http" || inner.scheme == "https" then inner.scheme ++ "://" ++ inner.hostWithPort else "null"
    | .error _ => "null"
  else "null"

end Urllib.Url
