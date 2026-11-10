import UrllibTest.Support
import Urllib.UrlPattern

namespace UrllibTest.UrlPattern.Units

open Urllib Urllib.UrlPattern

instance {α : Type} [BEq α] : BEq (Except Error α) where
  beq a b :=
    match a, b with
    | .ok x, .ok y => x == y
    | .error e, .error f => e == f
    | _, _ => false

def patternOf (init : Init) (options : UrlPatternOptions := {}) : Option UrlPattern :=
  (UrlPattern.create (.init init) none options).toOption

def pathnameOf (text : String) : Option UrlPattern :=
  patternOf { pathname := some text }

def tokens (text : String) (policy : Policy := .strict) : Option (List (TokenType × String)) :=
  (tokenize text policy).toOption.map fun ts => ts.map fun t => (t.type, t.value)

def part (type : PartType) (value : String) (modifier : Modifier) (name : String := "") (leading : String := "") (trailing : String := "") : Part :=
  { type, value, modifier, name, leading, trailing }

def checks : List UrllibTest.Check := [
  { name := "a hostname pattern with a bracket is an IPv6 pattern", holds := isIpv6Pattern "[::1]" },
  { name := "a bracket after a brace is an IPv6 pattern", holds := isIpv6Pattern "{[::1]}" },
  { name := "an escaped bracket is an IPv6 pattern", holds := isIpv6Pattern "\\[::1]" },
  { name := "a lone bracket is not an IPv6 pattern", holds := !isIpv6Pattern "[" },
  { name := "a pattern without a bracket is not an IPv6 pattern", holds := !isIpv6Pattern "a[" && !isIpv6Pattern "{a" && !isIpv6Pattern "\\a" && !isIpv6Pattern "" },
  { name := "a pattern of the other kinds is not an IPv6 pattern when the second code point is not a bracket", holds := !isIpv6Pattern "{{" && !isIpv6Pattern "\\\\" },
  { name := "a slash is an absolute pathname", holds := isAbsolutePathname "/a" .url && isAbsolutePathname "/a" .pattern },
  { name := "an empty pathname is not absolute", holds := !isAbsolutePathname "" .pattern && !isAbsolutePathname "" .url },
  { name := "a pattern also takes an escaped or grouped slash as absolute", holds := isAbsolutePathname "\\/a" .pattern && isAbsolutePathname "{/a}" .pattern },
  { name := "a URL pathname starting with an escape is not absolute", holds := !isAbsolutePathname "\\/a" .url && !isAbsolutePathname "{/a}" .url },
  { name := "a pattern that starts with another code point is not absolute", holds := !isAbsolutePathname "a/" .pattern && !isAbsolutePathname "\\a" .pattern && !isAbsolutePathname "{a" .pattern && !isAbsolutePathname "a" .pattern },
  { name := "one trailing colon is stripped", holds := stripTrailingColon "https:" == "https" && stripTrailingColon "a::" == "a:" && stripTrailingColon "a" == "a" && stripTrailingColon "" == "" },
  { name := "one leading character is stripped when it matches", holds := stripLeading '?' "?a?" == "a?" && stripLeading '?' "a" == "a" && stripLeading '#' "" == "" },
  { name := "the last slash is found in code points", holds := lastSlashIndex "/a/b" == some 2 && lastSlashIndex "ab" == none && lastSlashIndex "" == none && lastSlashIndex "é/" == some 1 },
  { name := "a base URL string is escaped for a pattern and kept for a URL", holds := processBaseUrlString "a*b" .pattern == "a\\*b" && processBaseUrlString "a*b" .url == "a*b" },
  { name := "a base URL fills the components that the init leaves out", holds :=
      (processInit { pathname := some "x", baseUrl := some "https://u:p@h:81/a/b?q#f" } .url).toOption.map (fun i => (i.protocol, i.hostname, i.port, i.pathname, i.search, i.hash, i.username, i.password)) ==
        some (some "https", some "h", some "81", some "/a/x", none, none, some "u", some "p") },
  { name := "a search in the init makes the later components come from the base", holds :=
      (processInit { search := some "?z", baseUrl := some "https://h/a?q#f" } .url).toOption.map (fun i => (i.pathname, i.search, i.hash)) == some (some "/a", some "z", none) },
  { name := "a hash in the init keeps the base for everything before it", holds :=
      (processInit { hash := some "#z", baseUrl := some "https://h/a?q#f" } .url).toOption.map (fun i => (i.pathname, i.search, i.hash)) == some (some "/a", some "q", some "z") },
  { name := "a hostname in the init stops the inheritance of the port", holds :=
      (processInit { hostname := some "x", baseUrl := some "https://h:81/a" } .url).toOption.map (fun i => (i.protocol, i.port, i.pathname)) == some (some "https", none, none) },
  { name := "a username in the init stops the inheritance of the password", holds :=
      (processInit { username := some "x", baseUrl := some "https://u:p@h/a" } .url).toOption.map (fun i => (i.username, i.password)) == some (some "x", none) },
  { name := "a base URL with no port gives the empty port", holds :=
      (processInit { pathname := some "/x", baseUrl := some "https://h/a" } .url).toOption.map (·.port) == some (some "") },
  { name := "a base URL without a host gives the empty hostname", holds :=
      (processInit { baseUrl := some "mailto:a@b" } .url).toOption.map (·.hostname) == some (some "") },
  { name := "a pattern init keeps the strings of the base as escaped patterns", holds :=
      (processInit { baseUrl := some "https://h/a+b?q*#f" } .pattern).toOption.map (fun i => (i.pathname, i.search)) == some (some "/a\\+b", some "q\\*") },
  { name := "an invalid base URL is an input error", holds := (processInit { baseUrl := some "nonsense" } .url) == .error .input },
  { name := "a relative pathname joins the directory of the base path", holds :=
      (processInit { pathname := some "c", baseUrl := some "https://h/a/b" } .url).toOption.map (·.pathname) == some (some "/a/c") },
  { name := "a relative pathname against a base without a slash is kept", holds :=
      (processInit { pathname := some "c", baseUrl := some "mailto:a" } .url).toOption.map (·.pathname) == some (some "c") },
  { name := "a pathname of a non-special protocol is an opaque pathname", holds :=
      (processInit { protocol := some "foo:", pathname := some "a b" } .url).toOption.map (·.pathname) == some (some "a b") },
  { name := "the empty protocol canonicalizes the pathname as for a special scheme", holds :=
      (processInit { pathname := some "/a b" } .url).toOption.map (·.pathname) == some (some "/a%20b") },
  { name := "a protocol that does not parse is an error when processing a URL", holds := (processInit { protocol := some "1x" } .url) == .error .canonicalize },
  { name := "a pattern init keeps its protocol without the trailing colon", holds :=
      (processInit { protocol := some "https:", search := some "?q", hash := some "#h" } .pattern).toOption.map (fun i => (i.protocol, i.search, i.hash)) == some (some "https", some "q", some "h") },
  { name := "the components of an init can be read and set by name", holds :=
      ComponentName.all.all fun c => ((({} : Init).set c (some "x")).get c) == some "x" },
  { name := "an IPv6 hostname is lowercased", holds := canonicalizeIpv6Hostname "[::A]" == .ok "[::a]" },
  { name := "an IPv6 hostname with another character is rejected", holds := canonicalizeIpv6Hostname "[::g]" == .error .canonicalize && canonicalizeIpv6Hostname "[::A.]" == .error .canonicalize },
  { name := "an empty value canonicalizes to itself", holds :=
      canonicalizeHash "" == .ok "" && canonicalizeSearch "" == .ok "" && canonicalizePathname "" == .ok "" &&
      canonicalizeOpaquePathname "" == .ok "" && canonicalizeHostname "" == .ok "" && canonicalizePort "" == .ok "" &&
      canonicalizeUsername "" == .ok "" && canonicalizePassword "" == .ok "" && canonicalizeProtocol "" == .ok "" },
  { name := "a hostname that the host parser rejects is an error", holds := canonicalizeHostname "a b" == .error .canonicalize },
  { name := "an opaque pathname that stops at a question mark keeps the text before it", holds := canonicalizeOpaquePathname "a b?c" == .ok "a b" },
  { name := "a port that is not a number is an error and a default port is dropped", holds :=
      canonicalizePort "x" == .error .canonicalize && canonicalizePort "80" (some "http") == .ok "" && canonicalizePort "80" == .ok "80" },
  { name := "a search or a hash is encoded", holds := canonicalizeSearch "a b" == .ok "a%20b" && canonicalizeHash "a b" == .ok "a%20b" },
  { name := "a pathname without a leading slash is encoded as a piece", holds := canonicalizePathname "a b" == .ok "a%20b" && canonicalizePathname "../a" == .ok "../a" },
  { name := "the tokens of a pattern string have their types and values", holds :=
      tokens "/:id(\\d+)*{a}?\\*" == some [(.char, "/"), (.name, "id"), (.regexp, "\\d+"), (.asterisk, "*"), (.groupOpen, "{"),
        (.char, "a"), (.groupClose, "}"), (.otherModifier, "?"), (.escapedChar, "*"), (.endOfInput, "")] },
  { name := "a modifier plus is an other-modifier token", holds := tokens "a+" == some [(.char, "a"), (.otherModifier, "+"), (.endOfInput, "")] },
  { name := "a trailing backslash is a strict error and a lenient invalid token", holds :=
      tokens "a\\" == none && tokens "a\\" .lenient == some [(.char, "a"), (.invalidChar, "\\"), (.endOfInput, "")] },
  { name := "a colon without a name is a strict error and a lenient invalid token", holds :=
      tokens ":" == none && tokens ":-" .lenient == some [(.invalidChar, ":"), (.char, "-"), (.endOfInput, "")] },
  { name := "an empty regexp group is a strict error and a lenient invalid token", holds :=
      tokens "()" == none && tokens "()" .lenient == some [(.invalidChar, "("), (.char, ")"), (.endOfInput, "")] },
  { name := "an unclosed regexp group is a strict error", holds := tokens "(a" == none && tokens "(a\\" == none && tokens "(" == none },
  { name := "a regexp group may contain a nested non-capturing group and escapes", holds :=
      tokens "(a(?:b)\\))" == some [(.regexp, "a(?:b)\\)"), (.endOfInput, "")] },
  { name := "a nested capturing group is an error", holds := tokens "(a(b))" == none && tokens "(a(" == none },
  { name := "a regexp group may not start with a question mark", holds := tokens "(?a)" == none },
  { name := "a non-ASCII code point in a regexp group is an error", holds := tokens "(é)" == none && tokens "(\\é)" == none },
  { name := "a name may contain non-ASCII identifier code points", holds := tokens ":café" == some [(.name, "café"), (.endOfInput, "")] && tokens ":a$_‌" == some [(.name, "a$_‌"), (.endOfInput, "")] },
  { name := "a name cannot start with a digit", holds := tokens ":1" == none && tokens ":$a" == some [(.name, "$a"), (.endOfInput, "")] },
  { name := "a pathname pattern with an optional group drops the prefix with it", holds :=
      (pathnameOf "/foo/:bar?/baz").map (fun p => p.pathname.regexp.test "/foo/baz") == some true },
  { name := "a repeated group with a prefix and a suffix matches several segments", holds :=
      (pathnameOf "/{:a/}+").map (fun p => p.pathname.regexp.test "/x/y/") == some true },
  { name := "a zero-or-more group with a prefix may be absent", holds :=
      (pathnameOf "/:a*").map (fun p => p.pathname.regexp.test "" && p.pathname.regexp.test "/x/y" && !p.pathname.regexp.test "/") == some true },
  { name := "a one-or-more group with a prefix matches one segment", holds :=
      (pathnameOf "/:a+").map (fun p => p.pathname.regexp.test "/x/y" && !p.pathname.regexp.test "/") == some true },
  { name := "a group with a prefix and a suffix is wrapped in braces in the pattern string", holds :=
      (pathnameOf "/a{b:c}d").map (·.pathname.patternString) == some "/a{b:c}d" },
  { name := "two parts that could merge are separated with braces in the pattern string", holds :=
      (pathnameOf "/:a{b}").map (·.pathname.patternString) == some "{/:a}b" },
  { name := "a named group followed by an escaped name character is grouped in the pattern string", holds :=
      (pathnameOf "/:a\\b").map (·.pathname.patternString) == some "{/:a}b" },
  { name := "a wildcard after fixed text and one after a group have their own forms", holds :=
      (pathnameOf "/a*").map (·.pathname.patternString) == some "/a*" && (pathnameOf "/:a*").map (·.pathname.patternString) == some "/:a*" },
  { name := "a numbered group is written as a regexp or a wildcard", holds :=
      (pathnameOf "/(.*)").map (·.pathname.patternString) == some "/*" && (pathnameOf "/*/(.*)").map (·.pathname.patternString) == some "/*/*" },
  { name := "a duplicate group name is an error", holds := (pathnameOf "/:a/:a").isNone },
  { name := "a missing close brace is an error", holds := (pathnameOf "/{a").isNone },
  { name := "a group with a modifier and no content keeps the fixed text", holds := (pathnameOf "/{a}?").isSome && (pathnameOf "/{}?").isSome },
  { name := "a custom regexp that does not compile is an error", holds := (pathnameOf "/(\\p{L})").isNone && (pathnameOf "/(a|*)").isNone },
  { name := "a regexp that uses an unsupported feature is an error", holds := (pathnameOf "/(?=a)").isNone },
  { name := "a port equal to the default port of a special protocol is dropped", holds :=
      (patternOf { protocol := some "https", port := some "443" }).map (·.port.patternString) == some "" },
  { name := "a port of a non-special protocol is kept", holds :=
      (patternOf { protocol := some "foo", port := some "443" }).map (·.port.patternString) == some "443" },
  { name := "a protocol without a default port keeps the port", holds :=
      (patternOf { protocol := some "file", port := some "443" }).map (·.port.patternString) == some "443" },
  { name := "a constructor string needs a protocol or a base", holds := (UrlPattern.create (.string "/a")).toOption.isNone },
  { name := "a constructor string with a base is accepted", holds := (UrlPattern.create (.string "/a") (some "https://h/")).toOption.isSome },
  { name := "a dictionary with a base argument is an error", holds := (UrlPattern.create (.init {}) (some "https://h/")).toOption.isNone },
  { name := "a URL cannot construct a pattern", holds := (UrlPattern.create (.url (match Url.parse "https://h/" with | .ok u => u | .error _ => { scheme := "", username := "", password := "", host := none, port := none, path := .list [], query := none, fragment := none }))).toOption.isNone },
  { name := "an opaque pathname pattern is used for a non-special protocol", holds :=
      (patternOf { protocol := some "foo", pathname := some "a b" }).map (·.pathname.patternString) == some "a b" },
  { name := "ignoring case is applied to the pathname, the search, and the hash", holds :=
      (patternOf { pathname := some "/a", search := some "b", hash := some "c" } { ignoreCase := true }).map (fun p =>
        p.pathname.regexp.test "/A" && p.search.regexp.test "B" && p.hash.regexp.test "C") == some true },
  { name := "ignoring case is not applied to the hostname", holds :=
      (patternOf { hostname := some "a" } { ignoreCase := true }).map (fun p => p.hostname.regexp.test "A") == some false },
  { name := "an IPv6 hostname pattern is canonicalized as an IPv6 hostname", holds :=
      (patternOf { hostname := some "[\\:\\:A]" }).map (·.hostname.patternString) == some "[\\:\\:a]" },
  { name := "a URL input is matched through its serialization", holds :=
      match UrlPattern.create (.string "https://example.com/:id") with
      | .ok p =>
        match p.exec (.url (match Url.parse "https://example.com/42" with | .ok u => u | .error _ => { scheme := "", username := "", password := "", host := none, port := none, path := .list [], query := none, fragment := none })) with
        | .ok (some r) => r.pathname.groups == [("id", some "42")] && r.inputs == [.string "https://example.com/42"]
        | _ => false
      | .error _ => false },
  { name := "a string input with a base is matched and both strings are inputs", holds :=
      match UrlPattern.create (.init { pathname := some "/a" }) with
      | .ok p => match p.exec (.string "/a") (some "https://h/") with
        | .ok (some r) => r.inputs == [.string "/a", .string "https://h/"]
        | _ => false
      | .error _ => false },
  { name := "a string input with an invalid base does not match", holds :=
      match UrlPattern.create (.init {}) with
      | .ok p => (p.test (.string "/a") (some "nonsense")) == .ok false
      | .error _ => false },
  { name := "a string input that does not parse does not match", holds :=
      match UrlPattern.create (.init {}) with
      | .ok p => (p.test (.string "nonsense")) == .ok false
      | .error _ => false },
  { name := "a dictionary input with a base is an error", holds :=
      match UrlPattern.create (.init {}) with
      | .ok p => (p.test (.init {}) (some "https://h/")).toOption.isNone
      | .error _ => false },
  { name := "a dictionary input that cannot be processed does not match", holds :=
      match UrlPattern.create (.init {}) with
      | .ok p => (p.test (.init { protocol := some "1x" })) == .ok false
      | .error _ => false },
  { name := "a group that takes no part in a match is none", holds :=
      match UrlPattern.create (.init { pathname := some "/:a?" }) with
      | .ok p => match p.exec (.init { pathname := some "" }) with
        | .ok (some r) => r.pathname.groups == [("a", none)]
        | _ => false
      | .error _ => false },
  { name := "generate fills a group and encodes the value", holds :=
      match UrlPattern.create (.init { pathname := some "/:a" }) with
      | .ok p => p.generate .pathname [("a", "x y")] == .ok "/x%20y"
      | .error _ => false },
  { name := "generate fails for a missing required group and accepts a missing optional one", holds :=
      match UrlPattern.create (.init { pathname := some "/:a" }), UrlPattern.create (.init { pathname := some "/:a?" }),
            UrlPattern.create (.init { pathname := some "/:a*" }), UrlPattern.create (.init { pathname := some "/:a+" }) with
      | .ok p, .ok q, .ok r, .ok s =>
        (p.generate .pathname []).toOption.isNone && q.generate .pathname [] == .ok "" &&
        r.generate .pathname [] == .ok "" && (s.generate .pathname []).toOption.isNone
      | _, _, _, _ => false },
  { name := "generate fails when a value contains the delimiter of a segment wildcard", holds :=
      match UrlPattern.create (.init { pathname := some "/:a" }) with
      | .ok p => (p.generate .pathname [("a", "x/y")]).toOption.isNone
      | .error _ => false },
  { name := "generate keeps a value with a delimiter for a full wildcard and for a pattern without delimiter", holds :=
      match UrlPattern.create (.init { pathname := some "/*" }), UrlPattern.create (.init { search := some ":a" }) with
      | .ok p, .ok q => p.generate .pathname [("0", "x/y")] == .ok "/x/y" && q.generate .search [("a", "x/y")] == .ok "x/y"
      | _, _ => false },
  { name := "generate fails for a fixed text with a modifier", holds :=
      match UrlPattern.create (.init { pathname := some "/{a}?" }) with
      | .ok p => (p.generate .pathname []).toOption.isNone
      | .error _ => false },
  { name := "generate fails when the value cannot be encoded", holds :=
      match UrlPattern.create (.init { hostname := some ":a" }) with
      | .ok p => (p.generate .hostname [("a", "a b")]).toOption.isNone
      | .error _ => false },
  { name := "equal texts compare as equal, shorter first, and by code unit", holds :=
      compareText "a" "a" == 0 && compareText "a" "ab" == -1 && compareText "ab" "a" == 1 && compareText "b" "a" == 1 &&
      compareText "a" "b" == -1 && compareText "" "💩" == 1 },
  { name := "fixed texts compare as text", holds := compareParts (part .fixedText "a" .none) (part .fixedText "b" .none) == -1 },
  { name := "a fixed text is more specific than a group", holds :=
      compareParts (part .fixedText "a" .none) (part .segmentWildcard "" .none "x") == 1 &&
      compareParts (part .segmentWildcard "" .none "x") (part .fixedText "a" .none) == -1 },
  { name := "a fixed text with a modifier counts as a regexp", holds :=
      compareParts (part .fixedText "a" .optional) (part .regexp "a" .optional "x") == 0 && effectiveType (part .fixedText "a" .optional) == .regexp },
  { name := "groups compare by their affixes first", holds :=
      compareParts (part .segmentWildcard "" .none "x" "a" "") (part .segmentWildcard "" .none "y" "b" "") == -1 },
  { name := "groups with equal modifiers compare by regexp text and then by kind", holds :=
      compareParts (part .regexp "a" .none "x") (part .regexp "b" .none "y") == -1 &&
      compareParts (part .regexp "a" .none "x") (part .segmentWildcard "" .none "y") == 1 &&
      compareParts (part .segmentWildcard "" .none "y") (part .regexp "a" .none "x") == -1 &&
      compareParts (part .segmentWildcard "" .none "x") (part .fullWildcard "" .none "y") == 1 &&
      compareParts (part .fullWildcard "" .none "y") (part .segmentWildcard "" .none "x") == -1 &&
      compareParts (part .fullWildcard "" .none "x") (part .fullWildcard "" .none "y") == 0 },
  { name := "fixed text with a modifier compares as an escaped regexp", holds :=
      compareParts (part .fixedText "a.b" .optional) (part .regexp "a\\.b" .optional "x") == 0 &&
      compareParts (part .regexp "a\\.b" .optional "x") (part .fixedText "a.b" .optional) == 0 &&
      compareParts (part .fixedText "b" .optional) (part .regexp "a" .optional "x") == 1 },
  { name := "groups with different modifiers compare by modifier", holds :=
      compareParts (part .fullWildcard "" .none "x") (part .fullWildcard "" .optional "y") == 1 &&
      compareParts (part .fullWildcard "" .optional "x") (part .fullWildcard "" .none "y") == -1 &&
      compareParts (part .fullWildcard "" .oneOrMore "x") (part .fullWildcard "" .zeroOrMore "y") == 1 &&
      compareParts (part .fullWildcard "" .zeroOrMore "x") (part .fullWildcard "" .oneOrMore "y") == -1 &&
      compareParts (part .fullWildcard "" .optional "x") (part .fullWildcard "" .zeroOrMore "y") == 1 &&
      compareParts (part .fullWildcard "" .zeroOrMore "x") (part .fullWildcard "" .optional "y") == -1 },
  { name := "neighbouring fixed texts are merged before comparing", holds :=
      (mergeFixedParts [part .fixedText "a" .none, part .fixedText "b" .none, part .fixedText "c" .optional, part .fixedText "d" .none]).map (·.value) == ["ab", "c", "d"] },
  { name := "a longer part list is more specific", holds :=
      compareLists [part .fixedText "a" .none] [] == 1 && compareLists [] [part .fixedText "a" .none] == -1 && compareLists [] [] == 0 &&
      compareLists [part .fixedText "a" .none, part .fixedText "b" .none] [part .fixedText "a" .none] == 1 }
]

/-- info: [] -/
#guard_msgs in
#eval UrllibTest.failedChecks checks

end UrllibTest.UrlPattern.Units
