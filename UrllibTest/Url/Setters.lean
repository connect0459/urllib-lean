import UrllibTest.Support
import UrllibTest.Url.SetterVectors
import Urllib.Url.Setters

namespace UrllibTest.Url

open Urllib

structure SetterVector where
  setter : String
  href : String
  newValue : String
  expected : List (String × String)

def pairsOf : List String → List (String × String)
  | key :: value :: rest => (key, value) :: pairsOf rest
  | _ => []

def parseSetterVector (record : String) : Option SetterVector :=
  match record.splitOn (String.singleton setterFieldSeparator) with
  | setter :: href :: newValue :: rest => some { setter, href, newValue, expected := pairsOf rest }
  | _ => none

def allSetterVectors : List SetterVector :=
  (setterVectors.splitOn (String.singleton setterRecordSeparator)).filterMap parseSetterVector

def applySetter (setter : String) (url : Url) (value : String) : Url :=
  match setter with
  | "protocol" => url.setProtocol value
  | "username" => url.setUsername value
  | "password" => url.setPassword value
  | "host" => url.setHost value
  | "hostname" => url.setHostname value
  | "port" => url.setPort value
  | "pathname" => url.setPathname value
  | "search" => url.setSearch value
  | "hash" => url.setHash value
  | _ => url

def component (url : Url) (key : String) : Option String :=
  match key with
  | "href" => some url.serialize
  | "protocol" => some url.protocol
  | "username" => some url.username
  | "password" => some url.password
  | "host" => some url.hostWithPort
  | "hostname" => some url.hostname
  | "port" => some url.portText
  | "pathname" => some url.pathname
  | "search" => some url.search
  | "hash" => some url.hash
  | "origin" => some url.origin
  | _ => none

def setterMismatches (v : SetterVector) : List String :=
  match Url.parse v.href with
  | .error _ => [s!"unparsable start: {repr v.href}"]
  | .ok url =>
    if v.setter == "href" then
      match Url.setHref v.newValue with
      | .error _ => [s!"href setter failed: {repr v.newValue}"]
      | .ok updated =>
        v.expected.filterMap fun (key, expected) =>
          if component updated key == some expected then none
          else some s!"href setter {key} of {repr v.newValue}"
    else
      let updated := applySetter v.setter url v.newValue
      v.expected.filterMap fun (key, expected) =>
        if component updated key == some expected then none
        else some s!"{v.setter} of {repr v.href} to {repr v.newValue}: {key} is {repr (component updated key)} instead of {repr expected}"

def setterFailures : List String := allSetterVectors.flatMap setterMismatches

/-- info: [] -/
#guard_msgs in
#eval setterFailures.take 20

structure AsciiVector where
  input : String
  output : Option String

def parseAsciiVector (record : String) : Option AsciiVector :=
  match record.splitOn (String.singleton setterFieldSeparator) with
  | [input, output] => some { input, output := if output.startsWith "S" then some (output.drop 1).toString else none }
  | _ => none

def allAsciiVectors : List AsciiVector :=
  (toasciiVectors.splitOn (String.singleton setterRecordSeparator)).filterMap parseAsciiVector

def asciiMismatches (v : AsciiVector) : List String :=
  let parsed := Url.parse ("https://" ++ v.input ++ "/x")
  let viaParse : List String :=
    match v.output, parsed with
    | some output, .ok url =>
      if url.hostWithPort == output && url.hostname == output && url.pathname == "/x" && url.serialize == "https://" ++ output ++ "/x" then []
      else [s!"toascii parse of {repr v.input}: {url.serialize}"]
    | some _, .error _ => [s!"toascii parse failure of {repr v.input}"]
    | none, .ok url => [s!"toascii missing failure of {repr v.input}: {url.serialize}"]
    | none, .error _ => []
  let viaSetters : List String :=
    match Url.parse "https://x/" with
    | .error _ => ["base"]
    | .ok base =>
      let hostSet := base.setHost v.input
      let hostnameSet := base.setHostname v.input
      let expectedHost := v.output.getD "x"
      (if hostSet.hostWithPort == expectedHost then [] else [s!"host setter with {repr v.input}: {hostSet.hostWithPort}"]) ++
      (if hostnameSet.hostname == expectedHost then [] else [s!"hostname setter with {repr v.input}: {hostnameSet.hostname}"])
  viaParse ++ viaSetters

def asciiFailures : List String := allAsciiVectors.flatMap asciiMismatches

/-- info: [] -/
#guard_msgs in
#eval asciiFailures.take 20

def url (text : String) : Url :=
  match Url.parse text with
  | .ok u => u
  | .error _ => { scheme := "", username := "", password := "", host := none, port := none,
                  path := .list [], query := none, fragment := none }

def checks : List UrllibTest.Check := [
  { name := "the vector files are loaded", holds := allSetterVectors.length + skippedSetterTests > 270 && allAsciiVectors.length > 80 },
  { name := "href setter parses a new URL", holds := (Url.setHref "http://h/p").toOption.map Url.serialize == some "http://h/p" },
  { name := "href setter fails on an invalid URL", holds := (Url.setHref "nonsense").toOption.isNone },
  { name := "username setter encodes with the userinfo set", holds := ((url "http://h/").setUsername "a b@c").username == "a%20b%40c" },
  { name := "username setter is ignored without a host", holds := ((url "mailto:x").setUsername "a").username == "" },
  { name := "username setter is ignored with an empty host", holds := ((url "file:///p").setUsername "a").username == "" },
  { name := "password setter encodes with the userinfo set", holds := ((url "http://h/").setPassword "p:q").password == "p%3Aq" },
  { name := "password setter is ignored for a file URL with a host", holds := ((url "file://h/p").setPassword "a").password == "" },
  { name := "port setter with the empty string removes the port", holds := ((url "http://h:8080/").setPort "").port == none },
  { name := "port setter drops a default port", holds := ((url "http://h:8080/").setPort "80").port == none },
  { name := "port setter keeps the digits it can read", holds := ((url "http://h/").setPort "81x").port == some 81 },
  { name := "port setter ignores a value that is not a number", holds := ((url "http://h:8080/").setPort "x").port == some 8080 },
  { name := "port setter ignores a number above 65535", holds := ((url "http://h:8080/").setPort "70000").port == some 8080 },
  { name := "port setter is ignored for a file URL", holds := ((url "file:///p").setPort "21").port == none },
  { name := "host setter replaces the host and the port", holds := ((url "http://h:1/").setHost "x:2").serialize == "http://x:2/" },
  { name := "host setter keeps the port when the value has none", holds := ((url "http://h:1/").setHost "x").serialize == "http://x:1/" },
  { name := "host setter is ignored for an opaque path", holds := ((url "mailto:a@b").setHost "x").serialize == "mailto:a@b" },
  { name := "hostname setter refuses a port", holds := ((url "http://h:1/").setHostname "x:2").serialize == "http://h:1/" },
  { name := "hostname setter replaces the host", holds := ((url "http://h:1/").setHostname "x").serialize == "http://x:1/" },
  { name := "hostname setter is ignored for an opaque path", holds := ((url "mailto:a@b").setHostname "x").serialize == "mailto:a@b" },
  { name := "host setter on a file URL goes through the file host state", holds := ((url "file:///p").setHost "LOCALHOST").serialize == "file:///p" },
  { name := "an empty host is refused for a special URL", holds := ((url "http://h/").setHost "").serialize == "http://h/" },
  { name := "an empty host is refused when credentials exist", holds := ((url "foo://u@h/").setHost "").serialize == "foo://u@h/" },
  { name := "an empty host is accepted for a non-special URL without credentials", holds := ((url "foo://h/").setHost "").serialize == "foo:///" },
  { name := "pathname setter replaces the path", holds := ((url "http://h/a/b").setPathname "/x/../y z").serialize == "http://h/y%20z" },
  { name := "pathname setter treats a question mark as data", holds := ((url "http://h/a").setPathname "/x?y#z").serialize == "http://h/x%3Fy%23z" },
  { name := "pathname setter is ignored for an opaque path", holds := ((url "mailto:a@b").setPathname "/x").serialize == "mailto:a@b" },
  { name := "pathname setter on a URL without a host starts with an empty segment", holds := ((url "foo:/a").setPathname "b").serialize == "foo:/b" },
  { name := "pathname setter on a non-special URL with an empty path", holds := ((url "foo://h").setPathname "").serialize == "foo://h" },
  { name := "search setter replaces the query and drops one question mark", holds := ((url "http://h/?a").setSearch "?b?c").serialize == "http://h/?b?c" },
  { name := "search setter with the empty string removes the query", holds := ((url "http://h/?a").setSearch "").query == none },
  { name := "search setter keeps a number sign as data", holds := ((url "http://h/").setSearch "a#b").serialize == "http://h/?a%23b" },
  { name := "hash setter replaces the fragment and drops one number sign", holds := ((url "http://h/#a").setHash "#b c").serialize == "http://h/#b%20c" },
  { name := "hash setter with the empty string removes the fragment", holds := ((url "http://h/#a").setHash "").fragment == none },
  { name := "protocol setter changes between special schemes", holds := ((url "http://h:8080/").setProtocol "https").serialize == "https://h:8080/" },
  { name := "protocol setter drops the port that becomes the default", holds := ((url "http://h:443/").setProtocol "https:").serialize == "https://h/" },
  { name := "protocol setter refuses to cross the special boundary", holds := ((url "http://h/").setProtocol "foo").serialize == "http://h/" },
  { name := "protocol setter refuses a special scheme for a non-special URL", holds := ((url "foo://h/").setProtocol "http").serialize == "foo://h/" },
  { name := "protocol setter refuses a scheme that does not start with a letter", holds := ((url "http://h/").setProtocol "1x").serialize == "http://h/" },
  { name := "protocol setter refuses file for a URL with credentials", holds := ((url "http://u@h/").setProtocol "file").serialize == "http://u@h/" },
  { name := "protocol setter refuses file for a URL with a port", holds := ((url "http://h:1/").setProtocol "file").serialize == "http://h:1/" },
  { name := "protocol setter refuses another scheme for a file URL with an empty host", holds := ((url "file:///p").setProtocol "http").serialize == "file:///p" },
  { name := "protocol setter ignores what follows the first colon", holds := ((url "http://h/").setProtocol "https:x").scheme == "https" },
  { name := "protocol setter removes tabs and newlines", holds := ((url "http://h/").setProtocol "ht\ttps").scheme == "https" },
  { name := "an empty host is refused when a port exists", holds := ((url "foo://h:1/").setHost "").serialize == "foo://h:1/" },
  { name := "protocol setter accepts file for a URL without credentials and port", holds := ((url "http://h/").setProtocol "file").serialize == "file://h/" },
  { name := "protocol setter refuses file for a URL with a password", holds := ((url "http://:p@h/").setProtocol "file").serialize == "http://:p@h/" },
  { name := "protocol setter changes a file URL with a host to a special scheme", holds := ((url "file://h/p").setProtocol "http").serialize == "http://h/p" },
  { name := "a URL with credentials has credentials", holds := (url "http://u@h/").hasCredentials },
  { name := "a URL with a password has credentials", holds := (url "http://:p@h/").hasCredentials },
  { name := "a URL without credentials has none", holds := !(url "http://h/").hasCredentials },
  { name := "a URL cannot have credentials without a host", holds := (url "mailto:x").cannotHaveCredentials },
  { name := "path segments of a list path are its segments", holds := (url "http://h/a/b").pathSegments == ["a", "b"] },
  { name := "an opaque path has no segments", holds := (url "mailto:a/b").pathSegments == [] },
  { name := "canParse accepts an absolute URL", holds := Url.canParse "http://h/" },
  { name := "canParse rejects a relative URL without a base", holds := !Url.canParse "x" },
  { name := "canParse accepts a relative URL with a base", holds := Url.canParse "x" (some "http://h/") },
  { name := "canParse rejects an invalid base", holds := !Url.canParse "http://h/" (some "x") },
  { name := "canParse rejects an invalid input with a valid base", holds := !Url.canParse "http://" (some "http://h/") },
  { name := "join resolves a reference against a URL", holds := ((url "http://h/a/b").join "../c").toOption.map Url.serialize == some "http://h/c" },
  { name := "join fails when the reference cannot be resolved", holds := ((url "mailto:a@b").join "x").toOption.isNone },
  { name := "search params are parsed from the query", holds := (url "http://h/?a=1&b=2&a=3").searchParams.getAll "a" == ["1", "3"] },
  { name := "search params of a URL without a query are empty", holds := (url "http://h/").searchParams.size == 0 }
]

/-- info: [] -/
#guard_msgs in
#eval UrllibTest.failedChecks checks

end UrllibTest.Url
