import Lean.Data.Json
import UrllibTest.Support
import UrllibTest.UrlPattern.Vectors
import Urllib.UrlPattern

namespace UrllibTest.UrlPattern

open Lean (Json)
open Urllib Urllib.UrlPattern

def field (j : Json) (key : String) : Option Json := (j.getObjVal? key).toOption

def str? (j : Json) : Option String := j.getStr?.toOption

def isObject (j : Json) : Bool := (j.getObj?).isOk

def items (j : Json) : List Json := ((j.getArr?).toOption.map Array.toList).getD []

def initOfJson (j : Json) : Init :=
  let s (key : String) : Option String := (field j key).bind str?
  { protocol := s "protocol", username := s "username", password := s "password", hostname := s "hostname",
    port := s "port", pathname := s "pathname", search := s "search", hash := s "hash", baseUrl := s "baseURL" }

def inputOfJson (j : Json) : Input :=
  match str? j with
  | some text => .string text
  | none => .init (initOfJson j)

def componentNames : List (String × ComponentName) :=
  [("protocol", .protocol), ("username", .username), ("password", .password), ("hostname", .hostname),
   ("port", .port), ("pathname", .pathname), ("search", .search), ("hash", .hash)]

def earlier : ComponentName → List String
  | .protocol => []
  | .hostname => ["protocol"]
  | .port => ["protocol", "hostname"]
  | .username => []
  | .password => []
  | .pathname => ["protocol", "hostname", "port"]
  | .search => ["protocol", "hostname", "port", "pathname"]
  | .hash => ["protocol", "hostname", "port", "pathname", "search"]

def baseComponent (url : Url) : ComponentName → String
  | .protocol => url.scheme
  | .username => url.username
  | .password => url.password
  | .hostname => url.hostname
  | .port => url.portText
  | .pathname => url.pathname
  | .search => (url.search.drop 1).toString
  | .hash => (url.hash.drop 1).toString

def expectedPattern (entry : Json) (args : List Json) (name : String) (c : ComponentName) : String :=
  let expectedObj := (field entry "expected_obj").getD (Json.mkObj [])
  match (field expectedObj name).bind str? with
  | some value => value
  | none =>
    let empties := ((field entry "exactly_empty_components").map items).getD []
    let first := args.head?
    let firstObject := first.any isObject
    let firstField := first.bind fun f => (field f name).bind str?
    let baseText : Option String :=
      match first.bind fun f => (field f "baseURL").bind str? with
      | some b => if b.isEmpty then none else some b
      | none =>
        match args[1]? with
        | some second => str? second
        | none => none
    if empties.any (fun e => str? e == some name) then ""
    else if firstObject && (firstField.any fun v => !v.isEmpty) then firstField.getD ""
    else if firstObject && (earlier c).any (fun e => first.any fun f => (field f e).isSome) then "*"
    else
      match baseText.bind fun b => (Url.parse b).toOption with
      | some baseUrl => if name == "username" || name == "password" then "*" else baseComponent baseUrl c
      | none => "*"

def optionsOf (args : List Json) : UrlPatternOptions :=
  let opt := args.drop 1 |>.filter isObject |>.head?
  { ignoreCase := match opt.bind fun o => (field o "ignoreCase") with
      | some v => (v.getBool?).toOption.getD false
      | none => false }

def baseOf (args : List Json) : Option String := (args.drop 1).head?.bind str?

def constructorInput (args : List Json) : Input :=
  match args.head? with
  | some f => inputOfJson f
  | none => .init {}

def groupsOf (j : Json) : List (String × Option String) :=
  match (j.getObj?).toOption with
  | some obj => obj.toArray.toList.map fun (k, v) => (k, str? v)
  | none => []

def sameGroups (actual : List (String × Option String)) (expected : List (String × Option String)) : Bool :=
  actual.length == expected.length && expected.all fun e => actual.contains e

def initFieldsEqual (a : Init) (b : Init) : Bool :=
  ComponentName.all.all fun c => a.get c == b.get c

def inputsEqual (actual : List Input) (expected : List Json) : Bool :=
  actual.length == expected.length &&
    (actual.zip expected).all fun (a, e) =>
      match a, str? e with
      | .string x, some y => x == y
      | .init i, none => initFieldsEqual i (initOfJson e)
      | _, _ => false

def matchMismatches (entry : Json) (label : String) (result : Result) (inputsJson : List Json) : List String :=
  let expectedMatch := (field entry "expected_match").getD Json.null
  let empties := ((field entry "exactly_empty_components").map items).getD []
  let expectedInputs := ((field expectedMatch "inputs").map items).getD inputsJson
  let inputCheck := if inputsEqual result.inputs expectedInputs then [] else [s!"{label}: inputs"]
  let componentChecks := componentNames.filterMap fun (name, c) =>
    let actual : ComponentResult :=
      match c with
      | .protocol => result.protocol | .username => result.username | .password => result.password
      | .hostname => result.hostname | .port => result.port | .pathname => result.pathname
      | .search => result.search | .hash => result.hash
    let expectedJson := field expectedMatch name
    let (expectedInput, expectedGroups) :=
      match expectedJson with
      | some e => (((field e "input").bind str?).getD "", groupsOf ((field e "groups").getD (Json.mkObj [])))
      | none => ("", if empties.any (fun x => str? x == some name) then [] else [("0", some "")])
    if actual.input == expectedInput && sameGroups actual.groups expectedGroups then none
    else some s!"{label}: {name} gives {repr actual} instead of {expectedInput} {repr expectedGroups}"
  inputCheck ++ componentChecks

def entryMismatches (entry : Json) : List String :=
  let args := items ((field entry "pattern").getD (Json.arr #[]))
  let label := s!"pattern {(field entry "pattern").map toString |>.getD ""} inputs {(field entry "inputs").map toString |>.getD ""}"
  let created := UrlPattern.create (constructorInput args) (baseOf args) (optionsOf args)
  match (field entry "expected_obj").bind str? with
  | some _ => match created with
    | .error _ => []
    | .ok _ => [s!"{label}: expected the constructor to fail"]
  | none =>
    match created with
    | .error e => [s!"{label}: constructor failed with {repr e}"]
    | .ok pattern =>
      let patternChecks := componentNames.filterMap fun (name, c) =>
        let expected := expectedPattern entry args name c
        let actual := (pattern.get c).patternString
        if actual == expected then none else some s!"{label}: {name} pattern is {repr actual} instead of {repr expected}"
      let inputsJson := ((field entry "inputs").map items).getD []
      let input := match inputsJson.head? with | some f => inputOfJson f | none => .init {}
      let base := (inputsJson.drop 1).head?.bind str?
      let expectedMatch := field entry "expected_match"
      match expectedMatch.bind str? with
      | some _ =>
        (match pattern.test input base with | .error _ => [] | .ok _ => [s!"{label}: expected test to fail"]) ++
        (match pattern.exec input base with | .error _ => [] | .ok _ => [s!"{label}: expected exec to fail"])
      | none =>
        let matched := expectedMatch.any fun m => isObject m
        let testChecks := match pattern.test input base with
          | .ok r => if r == matched then [] else [s!"{label}: test gives {r}"]
          | .error e => [s!"{label}: test failed with {repr e}"]
        let execChecks := match pattern.exec input base with
          | .error e => [s!"{label}: exec failed with {repr e}"]
          | .ok none => if matched then [s!"{label}: exec found no match"] else []
          | .ok (some result) => if matched then matchMismatches entry label result inputsJson else [s!"{label}: unexpected match"]
        patternChecks ++ testChecks ++ execChecks

def allEntries : List Json :=
  match Json.parse vectors with
  | .ok j => items j
  | .error _ => []

def failures : List String := allEntries.flatMap entryMismatches

/-- info: [] -/
#guard_msgs in
#eval failures.take 30

def componentOf (name : String) : Option ComponentName :=
  (componentNames.find? fun (n, _) => n == name).map (·.2)

def initPattern (j : Json) : Option UrlPattern :=
  (UrlPattern.create (inputOfJson j)).toOption

def compareMismatches (entry : Json) : List String :=
  let component := (field entry "component").bind str? |>.bind componentOf
  let left := (field entry "left").bind initPattern
  let right := (field entry "right").bind initPattern
  let expected := (field entry "expected").bind fun e => (e.getInt?).toOption
  match component, left, right, expected with
  | some c, some l, some r, some e =>
    if UrlPattern.compareComponent c l r == e then [] else [s!"compare {entry}"]
  | _, _, _, _ => [s!"unreadable compare entry {entry}"]

def compareFailures : List String :=
  match Json.parse compareVectors with
  | .ok j => (items j).flatMap compareMismatches
  | .error _ => ["compare data"]

/-- info: [] -/
#guard_msgs in
#eval compareFailures.take 20

def generateMismatches (entry : Json) : List String :=
  let pattern := (field entry "pattern").bind initPattern
  let component := (field entry "component").bind str? |>.bind componentOf
  let groups : List (String × String) :=
    match (field entry "groups").bind fun g => (g.getObj?).toOption with
    | some obj => obj.toArray.toList.filterMap fun (k, v) => (str? v).map (k, ·)
    | none => []
  let expected := (field entry "expected").bind str?
  match pattern with
  | none => [s!"unreadable pattern {entry}"]
  | some p =>
    match component with
    | none => if expected.isNone then [] else [s!"unknown component accepted {entry}"]
    | some c =>
      match p.generate c groups, expected with
      | .ok text, some e => if text == e then [] else [s!"generate gives {text} for {entry}"]
      | .error _, none => []
      | .ok text, none => [s!"generate gave {text} but must fail for {entry}"]
      | .error _, some _ => [s!"generate failed for {entry}"]

def generateFailures : List String :=
  match Json.parse generateVectors with
  | .ok j => (items j).flatMap generateMismatches
  | .error _ => ["generate data"]

/-- info: [] -/
#guard_msgs in
#eval generateFailures.take 20

def hasGroups (name : ComponentName) (value : String) : Bool :=
  match UrlPattern.create (.init ((({} : Init).set name (some value)))) with
  | .ok p => p.hasRegexpGroups
  | .error _ => false

def hasRegexpGroupsChecks : List UrllibTest.Check :=
  [ { name := "a match-everything pattern has no regexp group", holds := match UrlPattern.create (.init {}) with | .ok p => !p.hasRegexpGroups | .error _ => false } ] ++
  (ComponentName.all.flatMap fun c =>
    [ { name := "a wildcard is not a regexp group", holds := !hasGroups c "*" },
      { name := "a segment wildcard is not a regexp group", holds := !hasGroups c ":foo" },
      { name := "an optional segment wildcard is not a regexp group", holds := !hasGroups c ":foo?" },
      { name := "a named regexp group is a regexp group", holds := hasGroups c ":foo(hi)" },
      { name := "an anonymous regexp group is a regexp group", holds := hasGroups c "(hi)" } ]) ++
  ([ComponentName.username, .password, .hostname, .pathname, .search, .hash].flatMap fun c =>
    [ { name := "wildcards mixed with fixed text are not regexp groups", holds := !hasGroups c "a-{:hello}-z-*-a" },
      { name := "regexp groups mixed with fixed text are regexp groups", holds := hasGroups c "a-(hi)-z-(lo)-a" } ]) ++
  [ { name := "a complex pathname without a regexp has no regexp group", holds := !hasGroups .pathname "/a/:foo/:baz?/b/*" },
    { name := "a complex pathname with a regexp has a regexp group", holds := hasGroups .pathname "/a/:foo/:baz([a-z]+)?/b/*" } ]

/-- info: [] -/
#guard_msgs in
#eval UrllibTest.failedChecks hasRegexpGroupsChecks

/-- The strings that the patterns of the vectors are made of. -/
def patternStrings : List String :=
  allEntries.flatMap fun entry =>
    (items ((field entry "pattern").getD (Json.arr #[]))).flatMap fun p =>
      match str? p with
      | some s => [s]
      | none =>
        (["protocol", "username", "password", "hostname", "port", "pathname", "search", "hash", "baseURL"].filterMap
          fun key => (field p key).bind str?)

def variants (s : String) : List String :=
  let cs := s.toList
  (List.range (cs.length + 1)).flatMap fun n =>
    [String.ofList (cs.take n), String.ofList (cs.drop n)] ++
      (if n < cs.length then [String.ofList (cs.take n ++ cs.drop (n + 1))] else [])

def survives (input : Input) : Bool :=
  match UrlPattern.create input none with
  | .ok p =>
    (match p.exec (.string "https://user:pw@example.com:8080/a/b?q=1#h") with | _ => true) &&
    (match p.exec (.init { pathname := some "/a" }) with | _ => true)
  | .error _ => true

def robustnessChecks : List UrllibTest.Check := [
  { name := "constructor strings cut from the test patterns never break the constructor", holds :=
      patternStrings.all fun s => (variants s).all fun v => survives (.string v) },
  { name := "component patterns cut from the test patterns never break the constructor", holds :=
      patternStrings.all fun s => (variants s).all fun v =>
        ComponentName.all.all fun c => survives (.init (({} : Init).set c (some v))) }
]

/-- info: [] -/
#guard_msgs in
#eval UrllibTest.failedChecks robustnessChecks

end UrllibTest.UrlPattern
