import UrllibTest.Support
import Urllib.Url.Setters

namespace UrllibTest.Url.SearchParams

open Urllib

def sp (query : String) : SearchParams := SearchParams.ofString query

def url (text : String) : Url :=
  match Url.parse text with
  | .ok u => u
  | .error _ => { scheme := "", username := "", password := "", host := none, port := none,
                  path := .list [], query := none, fragment := none }

def empty : SearchParams := { pairs := [] }

def sortedPairs (input : String) : List (String × String) := (sp input).sort.pairs

def sortedViaUrl (input : String) : List (String × String) :=
  (SearchParams.ofString (((url "https://example/").setSearch ("?" ++ input)).updateSearchParams (·.sort)).search).pairs

def sortCases : List (String × List (String × String)) := [
  ("z=b&a=b&z=a&a=a", [("a", "b"), ("a", "a"), ("z", "b"), ("z", "a")]),
  ("�=x&￼&�=a", [("￼", ""), ("�", "x"), ("�", "a")]),
  ("ﬃ&🌈", [("🌈", ""), ("ﬃ", "")]),
  ("é&e�&é", [("é", ""), ("e�", ""), ("é", "")]),
  ("z=z&a=a&z=y&a=b&z=x&a=c&z=w&a=d&z=v&a=e&z=u&a=f&z=t&a=g",
    [("a", "a"), ("a", "b"), ("a", "c"), ("a", "d"), ("a", "e"), ("a", "f"), ("a", "g"),
     ("z", "z"), ("z", "y"), ("z", "x"), ("z", "w"), ("z", "v"), ("z", "u"), ("z", "t")]),
  ("bbb&bb&aaa&aa=x&aa=y", [("aa", "x"), ("aa", "y"), ("aaa", ""), ("bb", ""), ("bbb", "")]),
  ("z=z&=f&=t&=x", [("", "f"), ("", "t"), ("", "x"), ("z", "z")]),
  ("a🌈&a💩", [("a🌈", ""), ("a💩", "")])
]

def checks : List UrllibTest.Check := [
  { name := "search params without input serialize as the empty string", holds := empty.toString == "" },
  { name := "a string of the input is parsed and serialized back", holds := (sp "a=b").toString == "a=b" },
  { name := "one leading question mark is removed from the input", holds := (sp "?a=b").toString == "a=b" },
  { name := "a name without a value, and an empty pair, parse as in the standard", holds := (sp "a=b&c").has "c" && (sp "a=b&c").has "a" && !(sp "a=b").has "b" },
  { name := "a messy query parses into its names", holds :=
      let p := sp "&a&&& &&&&&a+b=& c&m%c3%b8%c3%b8"
      p.has "a" && p.has "a b" && p.has " " && !p.has "c" && p.has " c" && p.has "møø" },
  { name := "an incomplete percent escape stays in the value", holds := (sp "id=0&value=%").get "value" == some "%" && (sp "id=0&value=%").get "id" == some "0" },
  { name := "an invalid escape is kept and a valid one after it is decoded", holds := (sp "b=%2sf%2a").get "b" == some "%2sf*" },
  { name := "a truncated escape before a valid one is kept", holds := (sp "b=%2%2af%2a").get "b" == some "%2*f*" },
  { name := "a percent sign before a valid escape is kept", holds := (sp "b=%%2a").get "b" == some "%*" },
  { name := "a plus sign in a value is a space", holds := (sp "a=b+c").get "a" == some "b c" && (sp "a+b=c").get "a b" == some "c" },
  { name := "a plus sign survives a round trip as an escape", holds :=
      let p := empty.set "query" "+15555555555"
      p.toString == "query=%2B15555555555" && (sp p.toString).get "query" == some "+15555555555" },
  { name := "a space in the input is kept", holds := (sp "a=b c").get "a" == some "b c" && (sp "a b=c").get "a b" == some "c" },
  { name := "an escaped space is decoded", holds := (sp "a=b%20c").get "a" == some "b c" && (sp "a%20b=c").get "a b" == some "c" },
  { name := "a NUL in the input is kept", holds := (sp "a=b\x00c").get "a" == some "b\x00c" && (sp "a\x00b=c").get "a\x00b" == some "c" },
  { name := "an escaped NUL is decoded", holds := (sp "a=b%00c").get "a" == some "b\x00c" && (sp "a%00b=c").get "a\x00b" == some "c" },
  { name := "a non-ASCII character is kept", holds := (sp "a=b⎄").get "a" == some "b⎄" && (sp "a⎄b=c").get "a⎄b" == some "c" },
  { name := "an escaped non-ASCII character is decoded", holds := (sp "a=b%e2%8e%84").get "a" == some "b⎄" && (sp "a%e2%8e%84b=c").get "a⎄b" == some "c" },
  { name := "a supplementary-plane character is kept", holds := (sp "a=b💩c").get "a" == some "b💩c" && (sp "a💩b=c").get "a💩b" == some "c" },
  { name := "an escaped supplementary-plane character is decoded", holds := (sp "a=b%f0%9f%92%a9c").get "a" == some "b💩c" && (sp "a%f0%9f%92%a9b=c").get "a💩b" == some "c" },
  { name := "appending the same name keeps every pair", holds :=
      let p := (empty.append "a" "b")
      p.toString == "a=b" && (p.append "a" "b").toString == "a=b&a=b" && ((p.append "a" "b").append "a" "c").toString == "a=b&a=b&a=c" },
  { name := "appending empty strings is serialized with an equals sign", holds := (empty.append "" "").toString == "=" && ((empty.append "" "").append "" "").toString == "=&=" },
  { name := "appending several names keeps the first value for get", holds :=
      let p := ((((empty.append "first" "1").append "second" "2").append "third" "").append "first" "10").append "first" "10"
      p.has "first" && p.get "first" == some "1" && p.get "second" == some "2" && p.get "third" == some "" },
  { name := "get returns the first value, and none for an absent name", holds :=
      (sp "a=b&c=d").get "a" == some "b" && (sp "a=b&c=d").get "c" == some "d" && (sp "a=b&c=d").get "e" == none &&
      (sp "a=b&c=d&a=e").get "a" == some "b" && (sp "=b&c=d").get "" == some "b" && (sp "a=&c=d&a=e").get "a" == some "" },
  { name := "get finds a name that has no value", holds :=
      let p := sp "first=second&third&&"
      p.has "first" && p.get "first" == some "second" && p.get "third" == some "" && p.get "fourth" == none },
  { name := "getAll returns every value in order", holds :=
      (sp "a=b&c=d").getAll "a" == ["b"] && (sp "a=b&c=d").getAll "e" == [] && (sp "a=b&c=d&a=e").getAll "a" == ["b", "e"] &&
      (sp "=b&c=d").getAll "" == ["b"] && (sp "a=&c=d&a=e").getAll "a" == ["", "e"] },
  { name := "getAll sees every value and set collapses them", holds :=
      let p := sp "a=1&a=2&a=3&a"
      p.getAll "a" == ["1", "2", "3", ""] && (p.set "a" "one").get "a" == some "one" && (p.set "a" "one").getAll "a" == ["one"] },
  { name := "delete removes every pair with the name", holds :=
      (((sp "a=b&c=d").delete "a").toString == "c=d") && (((sp "a=a&b=b&a=a&c=c").delete "a").toString == "b=b&c=c") &&
      (((sp "a=a&=&b=b&c=c").delete "").toString == "a=a&b=b&c=c") },
  { name := "delete of the names null and undefined as plain strings", holds :=
      ((sp "a=a&null=null&b=b").delete "null").toString == "a=a&b=b" && ((sp "a=a&undefined=undefined&b=b").delete "undefined").toString == "a=a&b=b" },
  { name := "deleting every appended value of a name removes the name", holds :=
      let p := (((empty.append "first" "1").append "first" "10").delete "first")
      !p.has "first" },
  { name := "delete with a value removes only the pairs with that value", holds :=
      let p := ((empty.append "a" "b").append "a" "c").append "a" "d"
      (p.delete "a" (some "c")).toString == "a=b&a=d" },
  { name := "delete with a value spares other names", holds :=
      let p := (((empty.append "a" "b").append "a" "c").append "b" "c").append "b" "d"
      ((p.delete "b" (some "c")).delete "a" none).toString == "b=d" },
  { name := "has finds names, including the empty name", holds :=
      (sp "a=b&c=d").has "a" && (sp "a=b&c=d").has "c" && !(sp "a=b&c=d").has "e" && (sp "=b&c=d").has "" && (sp "null=a").has "null" },
  { name := "has follows delete", holds :=
      let p := ((sp "a=b&c=d&&").append "first" "1").append "first" "2"
      p.has "a" && p.has "c" && p.has "first" && !p.has "d" && !(p.delete "first").has "first" },
  { name := "has with a value requires both to match", holds :=
      let p := sp "a=b&a=d&c&e&"
      p.has "a" (some "b") && !p.has "a" (some "c") && p.has "a" (some "d") && p.has "e" (some "") &&
      !((p.append "first" "null").has "first" (some "")) && (p.append "first" "null").has "first" (some "null") &&
      (p.delete "a" (some "b")).has "a" (some "d") },
  { name := "has without a value matches any value", holds := (sp "a=b&a=d&c&e&").has "a" none },
  { name := "set replaces the first pair and drops the others", holds :=
      ((sp "a=b&c=d").set "a" "B").toString == "a=B&c=d" && ((sp "a=b&c=d&a=e").set "a" "B").toString == "a=B&c=d" &&
      (((sp "a=b&c=d&a=e").set "a" "B").set "e" "f").toString == "a=B&c=d&e=f" },
  { name := "set keeps the other names", holds :=
      let p := sp "a=1&a=2&a=3"
      (p.set "first" "4").get "a" == some "1" && (p.set "a" "4").get "a" == some "4" },
  { name := "size counts every pair", holds := (sp "a=1&b=2&a=3").size == 3 && ((sp "a=1&b=2&a=3").delete "a").size == 1 && ((sp "a=1&b=2&a=3").append "b" "4").size == 4 },
  { name := "serializing a space gives a plus sign", holds := (empty.append "a" "b c").toString == "a=b+c" && (empty.append "a b" "c").toString == "a+b=c" },
  { name := "serializing empty values", holds :=
      let p := empty.append "a" ""
      p.toString == "a=" && (p.append "a" "").toString == "a=&a=" && ((p.append "a" "").append "" "b").toString == "a=&a=&=b" },
  { name := "serializing an empty name", holds := (empty.append "" "b").toString == "=b" && ((empty.append "" "b").append "" "b").toString == "=b&=b" },
  { name := "serializing a plus sign", holds := (empty.append "a" "b+c").toString == "a=b%2Bc" && (empty.append "a+b" "c").toString == "a%2Bb=c" },
  { name := "serializing an equals sign", holds := (empty.append "=" "a").toString == "%3D=a" && ((empty.append "=" "a").append "b" "=").toString == "%3D=a&b=%3D" },
  { name := "serializing an ampersand", holds := (empty.append "&" "a").toString == "%26=a" && ((empty.append "&" "a").append "b" "&").toString == "%26=a&b=%26" },
  { name := "serializing asterisk, hyphen, dot and underscore", holds := (empty.append "a" "*-._").toString == "a=*-._" && (empty.append "*-._" "c").toString == "*-._=c" },
  { name := "serializing a percent sign", holds := (empty.append "a" "b%c").toString == "a=b%25c" && (empty.append "a%b" "c").toString == "a%25b=c" && (sp "id=0&value=%").toString == "id=0&value=%25" },
  { name := "serializing a NUL", holds := (empty.append "a" "b\x00c").toString == "a=b%00c" && (empty.append "a\x00b" "c").toString == "a%00b=c" },
  { name := "serializing a supplementary-plane character", holds := (empty.append "a" "b💩c").toString == "a=b%F0%9F%92%A9c" && (empty.append "a💩b" "c").toString == "a%F0%9F%92%A9b=c" },
  { name := "serializing normalizes the input", holds :=
      (sp "a=b&c=d&&e&&").toString == "a=b&c=d&e=" && (sp "a = b &a=b&c=d%20").toString == "a+=+b+&a=b&c=d+" &&
      (sp "a=&a=b").toString == "a=&a=b" && (sp "b=%2sf%2a").toString == "b=%252sf*" &&
      (sp "b=%2%2af%2a").toString == "b=%252*f*" && (sp "b=%%2a").toString == "b=%25*" },
  { name := "serializing does not normalize newlines", holds :=
      ((empty.append "a\nb" "c\rd").append "e\n\rf" "g\r\nh").toString == "a%0Ab=c%0Dd&e%0A%0Df=g%0D%0Ah" },
  { name := "every sort case gives the expected order", holds := sortCases.all fun (input, expected) => sortedPairs input == expected },
  { name := "every sort case gives the expected order through a URL", holds := sortCases.all fun (input, expected) => sortedViaUrl input == expected },
  { name := "a URL exposes the pairs of its query", holds := (url "http://example.org/?a=b").searchParams.toString == "a=b" },
  { name := "setting a pair that exists leaves the URL as it is", holds := (((url "http://example.org/?a=b").updateSearchParams (·.set "a" "b")).search == "?a=b") },
  { name := "clearing the search clears the params", holds := (((url "http://example.org/?a=b").setSearch "").searchParams.toString == "") },
  { name := "a search set on the URL is reflected in the params", holds :=
      let u := (url "http://example.org/file?a=b&c=d").setSearch "e=f&g=h"
      u.search == "?e=f&g=h" && u.searchParams.toString == "e=f&g=h" },
  { name := "a search set with a leading question mark is reflected in the params", holds :=
      let u := (url "http://example.org/file?a=b&c=d").setSearch "?e=f&g=h"
      u.search == "?e=f&g=h" && u.searchParams.toString == "e=f&g=h" },
  { name := "appending a param updates the search", holds :=
      let u := ((url "http://example.org/file?a=b&c=d").setSearch "?e=f&g=h").updateSearchParams (·.append "i" " j ")
      u.search == "?e=f&g=h&i=+j+" && u.searchParams.toString == "e=f&g=h&i=+j+" && u.searchParams.get "i" == some " j " },
  { name := "setting a param updates the search in place", holds :=
      let u := (((url "http://example.org/file?a=b&c=d").setSearch "?e=f&g=h").updateSearchParams (·.append "i" " j ")).updateSearchParams (·.set "e" "updated")
      u.search == "?e=updated&g=h&i=+j+" && u.searchParams.get "e" == some "updated" },
  { name := "a second question mark belongs to the first name", holds :=
      let u := url "http://example.org/file??a=b&c=d"
      u.search == "??a=b&c=d" && u.searchParams.toString == "%3Fa=b&c=d" },
  { name := "a new href is reflected in the params", holds :=
      match Url.setHref "http://example.org/file??a=b" with
      | .ok u => u.search == "??a=b" && u.searchParams.toString == "%3Fa=b"
      | .error _ => false },
  { name := "serializing the params of a URL escapes a comma", holds :=
      let u := url "http://www.example.com/?a=b,c"
      u.serialize == "http://www.example.com/?a=b,c" && u.searchParams.toString == "a=b%2Cc" &&
      (u.updateSearchParams (·.append "x" "y")).serialize == "http://www.example.com/?a=b%2Cc&x=y" },
  { name := "params of a URL do not normalize newlines", holds :=
      (((url "http://www.example.com/").updateSearchParams (·.append "a\nb" "c\rd")).updateSearchParams (·.append "e\n\rf" "g\r\nh")).searchParams.toString == "a%0Ab=c%0Dd&e%0A%0Df=g%0D%0Ah" },
  { name := "sorting the params of an empty query removes the question mark", holds :=
      let u := (url "http://example.com/?").updateSearchParams (·.sort)
      u.serialize == "http://example.com/" && u.search == "" },
  { name := "deleting every param removes the question mark", holds :=
      let u := ((url "http://example.com/?param1&param2").updateSearchParams (·.delete "param1")).updateSearchParams (·.delete "param2")
      u.serialize == "http://example.com/" && u.search == "" },
  { name := "deleting a param that does not exist removes the question mark of an empty query", holds :=
      let u := (url "http://example.com/?").updateSearchParams (·.delete "param1")
      u.serialize == "http://example.com/" && u.search == "" },
  { name := "changing the query of an opaque path with trailing spaces keeps the encoded space", holds :=
      let u := url "data:space    ?test"
      let v := u.updateSearchParams (·.delete "test")
      u.searchParams.has "test" && !v.searchParams.has "test" && v.search == "" && v.pathname == "space   %20" && v.serialize == "data:space   %20" },
  { name := "changing the query of an opaque path with trailing spaces and a fragment", holds :=
      let v := (url "data:space    ?test#test").updateSearchParams (·.delete "test")
      v.search == "" && v.pathname == "space   %20" && v.serialize == "data:space   %20#test" },
  { name := "the size of the params of a URL follows deletion and addition", holds :=
      let u := url "http://localhost/query?a=1&b=2&a=3"
      let v := u.updateSearchParams (·.delete "a")
      u.searchParams.size == 3 && v.searchParams.size == 1 && (v.updateSearchParams (·.append "b" "4")).searchParams.size == 2 },
  { name := "setting the search to a lone question mark empties the params", holds :=
      ((url "http://localhost/query?a=1&b=2&a=3").setSearch "?").searchParams.size == 0 }
]

/-- info: [] -/
#guard_msgs in
#eval UrllibTest.failedChecks checks

end UrllibTest.Url.SearchParams
