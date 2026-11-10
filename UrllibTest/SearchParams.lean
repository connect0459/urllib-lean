import UrllibTest.Support
import Urllib.SearchParams

namespace UrllibTest.SearchParams

open Urllib Urllib.SearchParams

def smile : String := String.singleton (Char.ofNat 0x1F600)

def privateUse : String := String.singleton (Char.ofNat 0xE000)

def ofPairs (pairs : List (String × String)) : SearchParams := { pairs := pairs }

def checks : List UrllibTest.Check := [
  { name := "an empty query string has no pairs", holds := (ofString "").pairs == [] },
  { name := "a query string is parsed as form-urlencoded", holds := (ofString "a=b+c&d=%41").pairs == [("a", "b c"), ("d", "A")] },
  { name := "one leading question mark is ignored", holds := (ofString "?a=1&b=2").pairs == [("a", "1"), ("b", "2")] },
  { name := "only one leading question mark is ignored", holds := (ofString "??a=1").pairs == [("?a", "1")] },
  { name := "a lone question mark has no pairs", holds := (ofString "?").pairs == [] },
  { name := "a question mark after the start is data", holds := (ofString "a?b=c").pairs == [("a?b", "c")] },
  { name := "pairs construct the list as given", holds := (ofPairs [("a", "b")]).pairs == [("a", "b")] },
  { name := "size counts pairs including repeated names", holds := (ofString "a=1&a=2&b=3").size == 3 },
  { name := "size of an empty list is zero", holds := (ofString "").size == 0 },
  { name := "append adds a pair at the end", holds := ((ofString "a=1").append "b" "2").pairs == [("a", "1"), ("b", "2")] },
  { name := "append keeps an existing pair with the same name", holds := ((ofString "a=1").append "a" "2").pairs == [("a", "1"), ("a", "2")] },
  { name := "append accepts empty strings", holds := ((ofString "").append "" "").pairs == [("", "")] },
  { name := "delete removes every pair with the name", holds := ((ofString "a=1&b=2&a=3").delete "a").pairs == [("b", "2")] },
  { name := "delete of an absent name changes nothing", holds := ((ofString "a=1").delete "z").pairs == [("a", "1")] },
  { name := "delete with a value removes only pairs matching both", holds := ((ofString "a=1&a=2&b=1").delete "a" (some "1")).pairs == [("a", "2"), ("b", "1")] },
  { name := "delete with an absent value changes nothing", holds := ((ofString "a=1").delete "a" (some "2")).pairs == [("a", "1")] },
  { name := "get returns the first value for the name", holds := (ofString "a=1&a=2").get "a" == some "1" },
  { name := "get of an absent name is none", holds := (ofString "a=1").get "b" == none },
  { name := "get returns an empty value as present", holds := (ofString "a=").get "a" == some "" },
  { name := "getAll returns every value in order", holds := (ofString "a=1&b=2&a=3").getAll "a" == ["1", "3"] },
  { name := "getAll of an absent name is empty", holds := (ofString "a=1").getAll "b" == [] },
  { name := "has finds a present name", holds := (ofString "a=1").has "a" },
  { name := "has does not find an absent name", holds := !(ofString "a=1").has "b" },
  { name := "has with a value requires both to match", holds := (ofString "a=1&a=2").has "a" (some "2") },
  { name := "has with a value that no pair carries is false", holds := !(ofString "a=1&b=2").has "a" (some "2") },
  { name := "set replaces the first value and removes the others", holds := ((ofString "a=1&b=2&a=3").set "a" "9").pairs == [("a", "9"), ("b", "2")] },
  { name := "set appends when the name is absent", holds := ((ofString "a=1").set "b" "2").pairs == [("a", "1"), ("b", "2")] },
  { name := "set keeps the position of the first pair", holds := ((ofString "b=0&a=1&c=2&a=3").set "a" "9").pairs == [("b", "0"), ("a", "9"), ("c", "2")] },
  { name := "sort orders pairs by name", holds := (ofString "c=1&a=2&b=3").sort.pairs == [("a", "2"), ("b", "3"), ("c", "1")] },
  { name := "sort keeps the relative order of equal names", holds := (ofString "b=1&a=2&b=0&a=1").sort.pairs == [("a", "2"), ("a", "1"), ("b", "1"), ("b", "0")] },
  { name := "sort places a prefix before its extension", holds := (ofString "ab=1&a=2").sort.pairs == [("a", "2"), ("ab", "1")] },
  { name := "sort places uppercase before lowercase", holds := (ofString "a=1&B=2").sort.pairs == [("B", "2"), ("a", "1")] },
  { name := "sort of an empty list is empty", holds := (ofString "").sort.pairs == [] },
  { name := "sort compares supplementary-plane names by UTF-16 units, placing them before U+E000", holds := (ofPairs [(privateUse, "1"), (smile, "2")]).sort.pairs == [(smile, "2"), (privateUse, "1")] },
  { name := "sort places a supplementary-plane name after a basic multilingual plane name below the surrogates", holds := (ofPairs [(smile, "1"), ("z", "2")]).sort.pairs == [("z", "2"), (smile, "1")] },
  { name := "UTF-16 units of a supplementary-plane code point are a surrogate pair", holds := utf16Units smile == [0xD83D, 0xDE00] },
  { name := "UTF-16 units of a basic multilingual plane code point are the code point", holds := utf16Units "aé" == [0x61, 0xE9] },
  { name := "toString serializes as form-urlencoded", holds := (ofPairs [("a b", "c&d")]).toString == "a+b=c%26d" },
  { name := "toString of an empty list is empty", holds := (ofString "").toString == "" },
  { name := "toString after parsing normalizes encoding", holds := (ofString "a=%41+b").toString == "a=A+b" },
  { name := "operations do not mutate the original", holds := let p := ofString "a=1"; let _ := p.append "b" "2"; p.pairs == [("a", "1")] }
]

/-- info: [] -/
#guard_msgs in
#eval UrllibTest.failedChecks checks

end UrllibTest.SearchParams
