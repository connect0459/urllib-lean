import Urllib.FormUrlencoded

namespace Urllib

/-- An ordered list of name-value pairs, the data model of the URL Standard's `URLSearchParams`. -/
structure SearchParams where
  /-- The pairs in insertion order. -/
  pairs : List (String × String)
  deriving DecidableEq, Repr

namespace SearchParams

/-- The UTF-16 code units of a string; a supplementary-plane code point becomes a surrogate pair. -/
def utf16Units (s : String) : List Nat :=
  s.toList.flatMap fun c =>
    let n := c.toNat
    if n < 0x10000 then [n]
    else
      let m := n - 0x10000
      [0xD800 + m / 0x400, 0xDC00 + m % 0x400]

/-- Lexicographic order on code unit lists, where a proper prefix is smaller. -/
def unitsLE : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if a == b then unitsLE as bs else false

/-- Compares two strings by UTF-16 code units, as the URL Standard's `sort` does. -/
def utf16LE (a b : String) : Bool :=
  unitsLE (utf16Units a) (utf16Units b)

/-- Parses a query string; one leading question mark is ignored. -/
def ofString (query : String) : SearchParams :=
  { pairs := FormUrlencoded.parse (if query.startsWith "?" then (query.drop 1).toString else query) }

/-- The number of pairs. -/
def size (p : SearchParams) : Nat :=
  p.pairs.length

/-- Appends a pair. -/
def append (p : SearchParams) (name value : String) : SearchParams :=
  { pairs := p.pairs ++ [(name, value)] }

/-- Removes every pair with the given name, and with the given value when one is supplied. -/
def delete (p : SearchParams) (name : String) (value : Option String := none) : SearchParams :=
  { pairs := p.pairs.filter fun (n, v) => !(n == name && value.all (· == v)) }

/-- The value of the first pair with the given name. -/
def get (p : SearchParams) (name : String) : Option String :=
  (p.pairs.find? fun (n, _) => n == name).map (·.2)

/-- The values of every pair with the given name, in order. -/
def getAll (p : SearchParams) (name : String) : List String :=
  (p.pairs.filter fun (n, _) => n == name).map (·.2)

/-- Whether a pair with the given name, and the given value when one is supplied, exists. -/
def has (p : SearchParams) (name : String) (value : Option String := none) : Bool :=
  p.pairs.any fun (n, v) => n == name && value.all (· == v)

/-- Sets the value of the first pair with the given name and removes the others; appends when the name is absent. -/
def set (p : SearchParams) (name value : String) : SearchParams :=
  if p.has name then
    let (pairs, _) := p.pairs.foldl
      (fun (acc : List (String × String) × Bool) (n, v) =>
        if n == name then
          if acc.2 then acc else (acc.1 ++ [(n, value)], true)
        else (acc.1 ++ [(n, v)], acc.2))
      ([], false)
    { pairs := pairs }
  else p.append name value

/-- Stably sorts the pairs by name in UTF-16 code unit order. -/
def sort (p : SearchParams) : SearchParams :=
  { pairs := p.pairs.mergeSort fun a b => utf16LE a.1 b.1 }

/-- Serializes the pairs as `application/x-www-form-urlencoded`. -/
protected def toString (p : SearchParams) : String :=
  FormUrlencoded.serialize p.pairs

instance : ToString SearchParams := ⟨SearchParams.toString⟩

end SearchParams

end Urllib
