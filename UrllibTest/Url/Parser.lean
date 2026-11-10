import UrllibTest.Support
import Urllib.Url.Parser

namespace UrllibTest.Url.Parser

open Urllib
open Urllib.Url.Parser

def parsed (input : String) (base : Option String := none) : Option String :=
  let baseUrl := base.bind fun b => (Url.parse b).toOption
  (Url.parse input baseUrl).toOption.map Url.serialize

def errorOf (input : String) (base : Option String := none) : Option Url.ParseError :=
  let baseUrl := base.bind fun b => (Url.parse b).toOption
  match Url.parse input baseUrl with
  | .error e => some e
  | .ok _ => none

def checks : List UrllibTest.Check := [
  { name := "a drive letter takes a letter and a colon", holds := isWindowsDriveLetter ['c', ':'] },
  { name := "a drive letter takes a letter and a vertical bar", holds := isWindowsDriveLetter ['C', '|'] },
  { name := "a character above z is not a drive letter", holds := !isWindowsDriveLetter ['{', ':'] },
  { name := "a character between Z and a is not a drive letter", holds := !isWindowsDriveLetter ['[', ':'] },
  { name := "a character below A is not a drive letter", holds := !isWindowsDriveLetter ['@', ':'] },
  { name := "a letter followed by another letter is not a drive letter", holds := !isWindowsDriveLetter ['c', 'd'] },
  { name := "a single code point is not a drive letter", holds := !isWindowsDriveLetter ['c'] },
  { name := "a normalized drive letter needs a colon", holds := isNormalizedWindowsDriveLetter ['c', ':'] && !isNormalizedWindowsDriveLetter ['c', '|'] },
  { name := "a character above z is not a normalized drive letter", holds := !isNormalizedWindowsDriveLetter ['{', ':'] },
  { name := "a character below A is not a normalized drive letter", holds := !isNormalizedWindowsDriveLetter ['@', ':'] },
  { name := "a drive letter at the end of the input starts a drive letter", holds := startsWithWindowsDriveLetter ['c', ':'] },
  { name := "a drive letter before a slash starts a drive letter", holds := startsWithWindowsDriveLetter "c:/x".toList },
  { name := "a drive letter before a letter does not start a drive letter", holds := !startsWithWindowsDriveLetter "c:x".toList },
  { name := "a lone letter does not start a drive letter", holds := !startsWithWindowsDriveLetter ['c'] },
  { name := "the empty list has no path segments when the path is opaque", holds := pathSegments (.opaque "x") == [] },
  { name := "a scheme must start with a letter above Z", holds := errorOf "{a:b" == some .missingBase },
  { name := "a scheme must start with a character between Z and a not being a letter", holds := errorOf "[a:b" == some .missingBase },
  { name := "a scheme must not start with a digit", holds := errorOf "1a:b" == some .missingBase },
  { name := "a scheme may contain digits, plus, hyphen, and dot", holds := parsed "a1+-.:b" == some "a1+-.:b" },
  { name := "a brace inside a would-be scheme makes the input relative", holds := parsed "a{b:c" (some "http://h/p/q") == some "http://h/p/a%7Bb:c" },
  { name := "a bracket inside a would-be scheme makes the input relative", holds := parsed "a[b:c" (some "http://h/p/q") == some "http://h/p/a[b:c" },
  { name := "a slash inside a would-be scheme makes the input relative", holds := parsed "a/b:c" (some "http://h/p/q") == some "http://h/p/a/b:c" },
  { name := "an uppercase scheme is lowercased", holds := parsed "HTTP://h/" == some "http://h/" },
  { name := "a scheme in uppercase letters up to Z is accepted", holds := parsed "ZZ:a" == some "zz:a" },
  { name := "a scheme with letters up to z is accepted", holds := parsed "zz:a" == some "zz:a" },
  { name := "a relative reference against a base with an opaque path fails", holds := errorOf "x" (some "mailto:a@b") == some .missingBase },
  { name := "a fragment against a base with an opaque path keeps the path", holds := parsed "#f" (some "mailto:a@b") == some "mailto:a@b#f" },
  { name := "an input without a scheme needs a base", holds := errorOf "x" == some .missingBase },
  { name := "credentials without a host fail", holds := errorOf "http://u:p@/" == some .hostMissing },
  { name := "an empty host of a special URL fails", holds := errorOf "http:///" == some .emptyHost },
  { name := "a port after an empty host fails", holds := errorOf "http://:80/" == some .emptyHost },
  { name := "a port above 65535 fails", holds := errorOf "http://h:65536/" == some .invalidPort },
  { name := "a non-digit in the port fails", holds := errorOf "http://h:8x/" == some .invalidPort },
  { name := "an empty port is dropped", holds := parsed "http://h:/" == some "http://h/" },
  { name := "the default port is dropped", holds := parsed "http://h:80/" == some "http://h/" },
  { name := "a non-default port is kept", holds := parsed "http://h:8080/" == some "http://h:8080/" },
  { name := "leading zeros of a port are read as a number", holds := parsed "http://h:0080/" == some "http://h/" },
  { name := "the largest port is accepted", holds := parsed "http://h:65535/" == some "http://h:65535/" },
  { name := "an invalid host is reported as a host error", holds := errorOf "http://a b/" == some (.host .forbiddenDomainCodePoint) },
  { name := "a non-special URL with an empty host keeps it empty", holds := parsed "foo://" == some "foo://" },
  { name := "a non-special URL takes an opaque host", holds := parsed "foo://H%41/" == some "foo://H%41/" },
  { name := "an input with no characters left after trimming has no scheme", holds := errorOf " \t\n" == some .missingBase },
  { name := "leading and trailing controls and spaces are trimmed", holds := parsed "\x01 http://h/ \x1f" == some "http://h/" },
  { name := "tabs and newlines inside the input are removed", holds := parsed "ht\ttp://h\n/\rp" == some "http://h/p" },
  { name := "the origin of an http URL is its scheme, host, and port", holds := (Url.parse "http://h:8080/p").toOption.map Url.origin == some "http://h:8080" },
  { name := "the origin of a file URL is opaque", holds := (Url.parse "file:///p").toOption.map Url.origin == some "null" },
  { name := "the origin of a blob URL is the origin of its https path", holds := (Url.parse "blob:https://h/uuid").toOption.map Url.origin == some "https://h" },
  { name := "the origin of a blob URL with a file path is opaque", holds := (Url.parse "blob:file:///x").toOption.map Url.origin == some "null" },
  { name := "the origin of a blob URL with an unparsable path is opaque", holds := (Url.parse "blob:x").toOption.map Url.origin == some "null" },
  { name := "the origin of an opaque-path URL is opaque", holds := (Url.parse "mailto:a@b").toOption.map Url.origin == some "null" }
]

/-- info: [] -/
#guard_msgs in
#eval UrllibTest.failedChecks checks

end UrllibTest.Url.Parser
