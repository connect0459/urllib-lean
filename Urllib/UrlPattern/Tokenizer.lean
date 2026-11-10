import Urllib.Unicode.Properties

namespace Urllib.UrlPattern

/-- Why URL Pattern construction or processing fails; each case corresponds to a `TypeError` of the specification. -/
inductive Error where
  /-- The tokenizer met an invalid code point in strict mode. -/
  | tokenizer
  /-- The pattern string is malformed: a missing token or a duplicate group name. -/
  | pattern
  /-- A component value is rejected by canonicalization. -/
  | canonicalize
  /-- A regular expression group is invalid or uses an unsupported feature. -/
  | regexp
  /-- The inputs of the constructor do not fit together, for example a base URL with a dictionary. -/
  | input
  deriving DecidableEq, Repr

/-- The kinds of token of a pattern string. -/
inductive TokenType where
  /-- `{`. -/
  | groupOpen
  /-- `}`. -/
  | groupClose
  /-- `(` ... `)`. -/
  | regexp
  /-- `:name`. -/
  | name
  /-- A code point without special meaning. -/
  | char
  /-- A backslash and the code point it escapes. -/
  | escapedChar
  /-- `?` or `+`. -/
  | otherModifier
  /-- `*`. -/
  | asterisk
  /-- The end of the input. -/
  | endOfInput
  /-- A code point that is invalid where it appears. -/
  | invalidChar
  deriving DecidableEq, Repr

/-- A token of a pattern string. -/
structure Token where
  /-- The kind of token. -/
  type : TokenType
  /-- The position of the first code point of the token. -/
  index : Nat
  /-- The code points that the token stands for. -/
  value : String
  deriving DecidableEq, Repr

/-- The tokenize policy: strict fails on an invalid code point, lenient makes an `invalid-char` token. -/
inductive Policy where
  /-- Fail on an invalid code point. -/
  | strict
  /-- Turn an invalid code point into a token. -/
  | lenient
  deriving DecidableEq, Repr

/-- Whether a code point can start a group name: it has the ID_Start property, or is a dollar sign or an underscore. -/
def isNameStart (c : Char) : Bool := Unicode.isIdStart c || c == '$' || c == '_'

/-- Whether a code point can continue a group name. -/
def isNamePart (c : Char) : Bool :=
  Unicode.isIdContinue c || c == '$' || c.toNat == 0x200C || c.toNat == 0x200D

/-- The code points from `start` of length `length`. -/
def substring (input : Array Char) (start length : Nat) : String :=
  String.ofList ((input.toList.drop start).take length)

/-- Scans the regular expression group that starts after the open parenthesis at `start - 1`: the position after the closing parenthesis, or none when the group is invalid. -/
def scanRegexp (input : Array Char) (start : Nat) : Option Nat :=
  go (input.size + 1) 1 start
where
  go (fuel depth pos : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match input[pos]? with
      | none => if depth == 0 then some pos else none
      | some c =>
        if c.toNat ≥ 128 then none
        else if pos == start && c == '?' then none
        else if c == '\\' then
          if pos + 1 == input.size then none
          else
            match input[pos + 1]? with
            | some d => if d.toNat ≥ 128 then none else go fuel depth (pos + 2)
            | none => none
        else if c == ')' then
          if depth == 1 then some (pos + 1) else go fuel (depth - 1) (pos + 1)
        else if c == '(' then
          if pos + 1 == input.size then none
          else if input[pos + 1]? == some '?' then go fuel (depth + 1) (pos + 1)
          else none
        else go fuel depth (pos + 1)

/-- The position after the longest name that starts at `pos`; `fuel` bounds the length. -/
def nameEnd (input : Array Char) (fuel start pos : Nat) : Nat :=
  match fuel with
  | 0 => pos
  | fuel + 1 =>
    match input[pos]? with
    | none => pos
    | some c => if (if pos == start then isNameStart c else isNamePart c) then nameEnd input fuel start (pos + 1) else pos

/-- Tokenizes a pattern string. -/
def tokenize (text : String) (policy : Policy) : Except Error (List Token) :=
  let input := text.toList.toArray
  let size := input.size
  let rec loop (fuel index : Nat) (acc : List Token) : Except Error (List Token) :=
    match fuel with
    | 0 => .ok (acc.reverse)
    | fuel + 1 =>
      if index < size then
        let add (type : TokenType) (next valuePos valueLen : Nat) : Except Error (List Token) :=
          loop fuel next ({ type := type, index := index, value := substring input valuePos valueLen } :: acc)
        let invalid (next valuePos : Nat) : Except Error (List Token) :=
          match policy with
          | .strict => .error .tokenizer
          | .lenient => add .invalidChar next valuePos (next - valuePos)
        match input[index]? with
        | none => .ok acc.reverse
        | some c =>
          if c == '*' then add .asterisk (index + 1) index 1
          else if c == '+' || c == '?' then add .otherModifier (index + 1) index 1
          else if c == '\\' then
            if index == size - 1 then invalid (index + 1) index
            else add .escapedChar (index + 2) (index + 1) 1
          else if c == '{' then add .groupOpen (index + 1) index 1
          else if c == '}' then add .groupClose (index + 1) index 1
          else if c == ':' then
            let start := index + 1
            let stop := nameEnd input (size + 1) start start
            if stop ≤ start then invalid start index
            else add .name stop start (stop - start)
          else if c == '(' then
            let start := index + 1
            match scanRegexp input start with
            | none => invalid start index
            | some after =>
              if after - start - 1 == 0 then invalid start index
              else add .regexp after start (after - start - 1)
          else add .char (index + 1) index 1
      else .ok ({ type := .endOfInput, index := index, value := "" } :: acc).reverse
  loop (size + 2) 0 []

end Urllib.UrlPattern
