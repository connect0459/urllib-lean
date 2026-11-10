namespace Urllib.Regex

/-- Why a regular expression is rejected: it is not valid JavaScript syntax, or it uses a feature that this engine does not support. -/
inductive Error where
  /-- The pattern is not valid in the unicode-sets mode. -/
  | syntax
  /-- The pattern uses lookaround, a backreference, a Unicode property escape, or a class string, which this engine does not support. -/
  | unsupported
  deriving DecidableEq, Repr

/-- A set of code points as written in a character class of the unicode-sets mode. -/
inductive ClassSet where
  /-- No code point. -/
  | empty
  /-- An inclusive range of code points; a single code point is a range of one. -/
  | range (low high : Char)
  /-- `\d`. -/
  | digit
  /-- `\D`. -/
  | notDigit
  /-- `\w`. -/
  | word
  /-- `\W`. -/
  | notWord
  /-- `\s`. -/
  | space
  /-- `\S`. -/
  | notSpace
  /-- The union of two sets. -/
  | union (left right : ClassSet)
  /-- The intersection of two sets. -/
  | inter (left right : ClassSet)
  /-- The first set without the second. -/
  | diff (left right : ClassSet)
  /-- The complement of a set. -/
  | neg (set : ClassSet)

/-- A regular expression syntax tree. -/
inductive Node where
  /-- A code point. -/
  | char (c : Char)
  /-- `.`: any code point but a line terminator. -/
  | any
  /-- A character class. -/
  | cls (set : ClassSet)
  /-- A sequence. -/
  | seq (nodes : List Node)
  /-- An alternation. -/
  | alt (nodes : List Node)
  /-- A group; capturing groups carry their index, counted from zero. -/
  | group (index : Option Nat) (node : Node)
  /-- A repetition with a minimum, an optional maximum, and greediness. -/
  | rep (node : Node) (min : Nat) (max : Option Nat) (greedy : Bool)
  /-- A repetition in progress, with the number of iterations done; used by the matcher only. -/
  | repState (node : Node) (min : Nat) (max : Option Nat) (greedy : Bool) (count : Nat)
  /-- `^`. -/
  | bol
  /-- `$`. -/
  | eol
  /-- `\b`. -/
  | wordBoundary
  /-- `\B`. -/
  | notWordBoundary

/-- A compiled regular expression. -/
structure Regex where
  /-- The syntax tree. -/
  node : Node
  /-- The number of capturing groups. -/
  groupCount : Nat
  /-- Whether matching ignores case. -/
  ignoreCase : Bool

/-- Whether a code point is a word character: an ASCII letter, a digit, or an underscore. -/
def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Whether a code point is white space or a line terminator in JavaScript. -/
def isSpaceChar (c : Char) : Bool :=
  let n := c.toNat
  n == 9 || n == 10 || n == 11 || n == 12 || n == 13 || n == 32 || n == 0xA0 || n == 0x1680 ||
    (0x2000 ≤ n && n ≤ 0x200A) || n == 0x2028 || n == 0x2029 || n == 0x202F || n == 0x205F ||
    n == 0x3000 || n == 0xFEFF

/-- Whether a code point is a line terminator. -/
def isLineTerminator (c : Char) : Bool :=
  let n := c.toNat
  n == 10 || n == 13 || n == 0x2028 || n == 0x2029

/-- Simple case folding as far as Lean core reaches: ASCII letters. -/
def fold (c : Char) : Char := c.toLower

/-- Whether a set contains the code point. -/
def ClassSet.contains (ignoreCase : Bool) (c : Char) : ClassSet → Bool
  | .empty => false
  | .range low high =>
    (low.toNat ≤ c.toNat && c.toNat ≤ high.toNat) ||
      (ignoreCase && ((low.toNat ≤ (fold c).toNat && (fold c).toNat ≤ high.toNat) ||
        (low.toNat ≤ c.toUpper.toNat && c.toUpper.toNat ≤ high.toNat)))
  | .digit => c.isDigit
  | .notDigit => !c.isDigit
  | .word => isWordChar c
  | .notWord => !isWordChar c
  | .space => isSpaceChar c
  | .notSpace => !isSpaceChar c
  | .union l r => l.contains ignoreCase c || r.contains ignoreCase c
  | .inter l r => l.contains ignoreCase c && r.contains ignoreCase c
  | .diff l r => l.contains ignoreCase c && !r.contains ignoreCase c
  | .neg s => !s.contains ignoreCase c

/-- The captures of the groups, as start and end positions. -/
abbrev Captures := List (Option (Nat × Nat))

/-- Sets the capture of a group. -/
def setCapture (caps : Captures) (index : Nat) (span : Nat × Nat) : Captures :=
  caps.mapIdx fun i old => if i == index then some span else old

/-- The backtracking matcher in continuation-passing style; `fuel` bounds the depth, and a match that runs out of fuel fails. -/
def matchNode (input : Array Char) (ignoreCase : Bool) :
    Nat → Node → Nat → Captures → (Nat → Captures → Option (Nat × Captures)) → Option (Nat × Captures)
  | 0, _, _, _, _ => none
  | fuel + 1, node, i, caps, k =>
    let at? (j : Nat) : Option Char := input[j]?
    match node with
    | .char c =>
      match at? i with
      | some d => if d == c || (ignoreCase && fold d == fold c) then k (i + 1) caps else none
      | none => none
    | .any =>
      match at? i with
      | some d => if isLineTerminator d then none else k (i + 1) caps
      | none => none
    | .cls cls =>
      match at? i with
      | some d => if cls.contains ignoreCase d then k (i + 1) caps else none
      | none => none
    | .seq [] => k i caps
    | .seq (first :: rest) =>
      matchNode input ignoreCase fuel first i caps fun j caps' => matchNode input ignoreCase fuel (.seq rest) j caps' k
    | .alt nodes => nodes.findSome? fun n => matchNode input ignoreCase fuel n i caps k
    | .group index n =>
      match index with
      | some idx => matchNode input ignoreCase fuel n i caps fun j caps' => k j (setCapture caps' idx (i, j))
      | none => matchNode input ignoreCase fuel n i caps k
    | .rep n min max greedy => matchNode input ignoreCase fuel (.repState n min max greedy 0) i caps k
    | .repState n min max greedy count =>
      let more : Option (Nat × Captures) :=
        if max == some count then none
        else
          matchNode input ignoreCase fuel n i caps fun j caps' =>
            if j == i && min ≤ count then none
            else matchNode input ignoreCase fuel (.repState n min max greedy (count + 1)) j caps' k
      let stop : Option (Nat × Captures) := if min ≤ count then k i caps else none
      if greedy then more <|> stop else stop <|> more
    | .bol => if i == 0 then k i caps else none
    | .eol => if i == input.size then k i caps else none
    | .wordBoundary =>
      let before := match i with | 0 => false | j + 1 => (at? j).any isWordChar
      let after := (at? i).any isWordChar
      if before != after then k i caps else none
    | .notWordBoundary =>
      let before := match i with | 0 => false | j + 1 => (at? j).any isWordChar
      let after := (at? i).any isWordChar
      if before == after then k i caps else none

/-- The number of nodes of a syntax tree, used to size the matcher's fuel. -/
def Node.size : Node → Nat
  | .seq nodes => 1 + sizeList nodes
  | .alt nodes => 1 + sizeList nodes
  | .group _ n => 1 + n.size
  | .rep n _ _ _ => 1 + n.size
  | .repState n _ _ _ _ => 1 + n.size
  | _ => 1
where
  sizeList : List Node → Nat
    | [] => 0
    | n :: rest => n.size + sizeList rest

/-- Runs the regular expression on the input, trying every start position; the result lists the groups as substrings, or none for a group that did not take part. -/
def Regex.exec (re : Regex) (input : String) : Option (List (Option String)) :=
  let chars := input.toList.toArray
  let fuel := 32 * (chars.size + re.node.size + 4)
  let rec attempt (start : Nat) (remaining : Nat) : Option (List (Option String)) :=
    match remaining with
    | 0 => none
    | r + 1 =>
      match matchNode chars re.ignoreCase fuel re.node start (List.replicate re.groupCount none) (fun j caps => some (j, caps)) with
      | some (_, caps) =>
        some (caps.map fun span => span.map fun (a, b) => String.ofList ((chars.toList.drop a).take (b - a)))
      | none => attempt (start + 1) r
  attempt 0 (chars.size + 1)

/-- Whether the regular expression matches somewhere in the input. -/
def Regex.test (re : Regex) (input : String) : Bool :=
  (re.exec input).isSome

end Urllib.Regex
