import Urllib.Regex

namespace Urllib.Regex

/-- The code points that must be escaped outside a character class. -/
def isSyntaxChar (c : Char) : Bool :=
  "^$\\.*+?()[]{}|/".toList.contains c

/-- The code points that must be escaped inside a character class of the unicode-sets mode. -/
def isClassSyntaxChar (c : Char) : Bool :=
  "()[]{}/-\\|".toList.contains c

/-- The code points that may follow a backslash inside a class as reserved punctuators. -/
def isClassReservedPunctuator (c : Char) : Bool :=
  "&-!#%,:;<=>@`~".toList.contains c

/-- The code points that make a reserved double punctuator when written twice in a class. -/
def isDoublePunctuator (c : Char) : Bool :=
  "!#$%*+,.:;<=>?@^`~".toList.contains c

/-- The value of a hexadecimal digit. -/
def hexValue? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

/-- The number that a list of hexadecimal digits spells, if they all are digits. -/
def hexNumber? (cs : List Char) : Option Nat :=
  cs.foldlM (fun acc c => (hexValue? c).map (acc * 16 + ·)) 0

/-- Whether a code point may start a group name. -/
def isNameStart (c : Char) : Bool := c.isAlpha || c == '_' || c == '$'

/-- Whether a code point may continue a group name. -/
def isNamePart (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$'

/-- A parsed escape: a code point or a class escape. -/
inductive Escape where
  /-- A code point. -/
  | char (c : Char)
  /-- `\\d`, `\\w`, `\\s` and their complements. -/
  | set (s : ClassSet)
  /-- `\\b`, kept apart because it means backspace inside a class. -/
  | boundary
  /-- `\\B`. -/
  | notBoundary

/-- Reads the escape after a backslash, in or out of a class; the result carries the rest of the input. -/
def parseEscape (inClass : Bool) (cs : List Char) : Except Error (Escape × List Char) :=
  match cs with
  | [] => .error .syntax
  | c :: rest =>
    match c with
    | 'd' => .ok (.set .digit, rest)
    | 'D' => .ok (.set .notDigit, rest)
    | 'w' => .ok (.set .word, rest)
    | 'W' => .ok (.set .notWord, rest)
    | 's' => .ok (.set .space, rest)
    | 'S' => .ok (.set .notSpace, rest)
    | 'b' => if inClass then .ok (.char (Char.ofNat 8), rest) else .ok (.boundary, rest)
    | 'B' => if inClass then .error .syntax else .ok (.notBoundary, rest)
    | 'n' => .ok (.char (Char.ofNat 10), rest)
    | 'r' => .ok (.char (Char.ofNat 13), rest)
    | 't' => .ok (.char (Char.ofNat 9), rest)
    | 'f' => .ok (.char (Char.ofNat 12), rest)
    | 'v' => .ok (.char (Char.ofNat 11), rest)
    | '0' =>
      match rest with
      | d :: _ => if d.isDigit then .error .syntax else .ok (.char (Char.ofNat 0), rest)
      | [] => .ok (.char (Char.ofNat 0), rest)
    | 'p' | 'P' | 'k' => .error .unsupported
    | 'c' =>
      match rest with
      | l :: rest' => if l.isAlpha then .ok (.char (Char.ofNat (l.toNat % 32)), rest') else .error .syntax
      | [] => .error .syntax
    | 'x' =>
      match rest with
      | a :: b :: rest' =>
        match hexNumber? [a, b] with
        | some n => .ok (.char (Char.ofNat n), rest')
        | none => .error .syntax
      | _ => .error .syntax
    | 'u' =>
      match rest with
      | '{' :: rest' =>
        let digits := rest'.takeWhile (· != '}')
        let after := rest'.drop (digits.length)
        match after, hexNumber? digits with
        | '}' :: tail, some n =>
          if digits.isEmpty || 0x10FFFF < n || (0xD800 ≤ n && n ≤ 0xDFFF) then .error .syntax
          else .ok (.char (Char.ofNat n), tail)
        | _, _ => .error .syntax
      | a :: b :: c' :: d :: rest' =>
        match hexNumber? [a, b, c', d] with
        | some n =>
          if 0xD800 ≤ n && n ≤ 0xDBFF then
            match rest' with
            | '\\' :: 'u' :: e :: f :: g :: h :: tail =>
              match hexNumber? [e, f, g, h] with
              | some m =>
                if 0xDC00 ≤ m && m ≤ 0xDFFF then
                  .ok (.char (Char.ofNat (0x10000 + (n - 0xD800) * 0x400 + (m - 0xDC00))), tail)
                else .error .syntax
              | none => .error .syntax
            | _ => .error .syntax
          else if 0xDC00 ≤ n && n ≤ 0xDFFF then .error .syntax
          else .ok (.char (Char.ofNat n), rest')
        | none => .error .syntax
      | _ => .error .syntax
    | _ =>
      if c.isDigit then .error .unsupported
      else if isSyntaxChar c || (inClass && isClassReservedPunctuator c) then .ok (.char c, rest)
      else .error .syntax

/-- The union of a list of sets. -/
def unionOf (sets : List ClassSet) : ClassSet :=
  sets.foldl ClassSet.union .empty

/-- A class operand: a code point or a set. -/
inductive Operand where
  /-- A single code point, which can start a range. -/
  | char (c : Char)
  /-- A set. -/
  | set (s : ClassSet)

/-- The set of an operand. -/
def Operand.toSet : Operand → ClassSet
  | .char c => .range c c
  | .set s => s

/-- Reads one operand of a class: a code point, an escape, or a nested class. -/
def parseOperand (parseNested : List Char → Except Error (ClassSet × List Char)) (cs : List Char) :
    Except Error (Operand × List Char) :=
  match cs with
  | [] => .error .syntax
  | '\\' :: rest =>
    match parseEscape true rest with
    | .ok (.char c, tail) => .ok (.char c, tail)
    | .ok (.set s, tail) => .ok (.set s, tail)
    | .ok (.boundary, _) => .error .syntax
    | .ok (.notBoundary, _) => .error .syntax
    | .error e => .error e
  | '[' :: rest =>
    match parseNested rest with
    | .ok (s, tail) => .ok (.set s, tail)
    | .error e => .error e
  | c :: rest =>
    if isClassSyntaxChar c then .error .syntax
    else if isDoublePunctuator c && rest.head? == some c then .error .syntax
    else .ok (.char c, rest)

/-- Reads the contents of a class up to and including the closing bracket. -/
def parseClassBody (fuel : Nat) (cs : List Char) : Except Error (ClassSet × List Char) :=
  match fuel with
  | 0 => .error .syntax
  | fuel + 1 =>
    let negated := cs.head? == some '^'
    let body := if negated then cs.drop 1 else cs
    let nested (rest : List Char) := parseClassBody fuel rest
    let finish (s : ClassSet) (rest : List Char) : Except Error (ClassSet × List Char) :=
      .ok ((if negated then ClassSet.neg s else s), rest)
    match body with
    | ']' :: rest => finish .empty rest
    | _ =>
      match parseOperand nested body with
      | .error e => .error e
      | .ok (first, rest) =>
        match rest with
        | '-' :: '-' :: rest' => parseOperators fuel nested ClassSet.diff first.toSet rest' finish
        | '&' :: '&' :: rest' => parseOperators fuel nested ClassSet.inter first.toSet rest' finish
        | _ => parseUnion fuel nested [] first rest finish
where
  parseOperators (fuel : Nat) (nested : List Char → Except Error (ClassSet × List Char))
      (combine : ClassSet → ClassSet → ClassSet) (acc : ClassSet) (cs : List Char)
      (finish : ClassSet → List Char → Except Error (ClassSet × List Char)) : Except Error (ClassSet × List Char) :=
    match fuel with
    | 0 => .error .syntax
    | fuel + 1 =>
      match parseOperand nested cs with
      | .error e => .error e
      | .ok (operand, rest) =>
        let acc' := combine acc operand.toSet
        match rest with
        | ']' :: tail => finish acc' tail
        | '-' :: '-' :: tail => if isDiff combine then parseOperators fuel nested combine acc' tail finish else .error .syntax
        | '&' :: '&' :: tail => if isDiff combine then .error .syntax else parseOperators fuel nested combine acc' tail finish
        | _ => .error .syntax
  isDiff (combine : ClassSet → ClassSet → ClassSet) : Bool :=
    match combine .empty .empty with
    | .diff _ _ => true
    | _ => false
  parseUnion (fuel : Nat) (nested : List Char → Except Error (ClassSet × List Char)) (acc : List ClassSet)
      (current : Operand) (cs : List Char)
      (finish : ClassSet → List Char → Except Error (ClassSet × List Char)) : Except Error (ClassSet × List Char) :=
    match fuel with
    | 0 => .error .syntax
    | fuel + 1 =>
      match cs with
      | '-' :: '-' :: _ => .error .syntax
      | '-' :: rest =>
        match current with
        | .set _ => .error .syntax
        | .char low =>
          match parseOperand nested rest with
          | .error e => .error e
          | .ok (.char high, rest') =>
            if high.toNat < low.toNat then .error .syntax
            else continueUnion fuel nested (.range low high :: acc) rest' finish
          | .ok (.set _, _) => .error .syntax
      | ']' :: rest => finish (unionOf (acc ++ [current.toSet])) rest
      | '&' :: '&' :: _ => .error .syntax
      | _ => continueUnion fuel nested (acc ++ [current.toSet]) cs finish
  continueUnion (fuel : Nat) (nested : List Char → Except Error (ClassSet × List Char)) (acc : List ClassSet)
      (cs : List Char) (finish : ClassSet → List Char → Except Error (ClassSet × List Char)) :
      Except Error (ClassSet × List Char) :=
    match fuel with
    | 0 => .error .syntax
    | fuel + 1 =>
      match cs with
      | ']' :: rest => finish (unionOf acc) rest
      | _ =>
        match parseOperand nested cs with
        | .error e => .error e
        | .ok (operand, rest) =>
          match rest with
          | '-' :: '-' :: _ => .error .syntax
          | '&' :: '&' :: _ => .error .syntax
          | _ => parseUnion fuel nested acc operand rest finish

/-- Reads decimal digits; none when there is no digit. -/
def parseNumber? (cs : List Char) : Option (Nat × List Char) :=
  let digits := cs.takeWhile Char.isDigit
  if digits.isEmpty then none
  else some (digits.foldl (fun acc d => acc * 10 + (d.toNat - 48)) 0, cs.drop digits.length)

/-- Reads a quantifier if one follows: the minimum, the maximum, greediness, and the rest. -/
def parseQuantifier (cs : List Char) : Except Error (Option (Nat × Option Nat × Bool × List Char)) :=
  let lazy (rest : List Char) : Bool × List Char :=
    match rest with
    | '?' :: tail => (false, tail)
    | _ => (true, rest)
  match cs with
  | '*' :: rest => let (g, r) := lazy rest; .ok (some (0, none, g, r))
  | '+' :: rest => let (g, r) := lazy rest; .ok (some (1, none, g, r))
  | '?' :: rest => let (g, r) := lazy rest; .ok (some (0, some 1, g, r))
  | '{' :: rest =>
    match parseNumber? rest with
    | none => .error .syntax
    | some (low, after) =>
      match after with
      | '}' :: tail => let (g, r) := lazy tail; .ok (some (low, some low, g, r))
      | ',' :: '}' :: tail => let (g, r) := lazy tail; .ok (some (low, none, g, r))
      | ',' :: more =>
        match parseNumber? more with
        | some (high, '}' :: tail) =>
          if high < low then .error .syntax else let (g, r) := lazy tail; .ok (some (low, some high, g, r))
        | _ => .error .syntax
      | _ => .error .syntax
  | _ => .ok none

mutual
/-- Reads a disjunction up to a closing parenthesis or the end; the result carries the rest and the number of groups so far. -/
def parseDisjunction : Nat → List Char → Nat → Except Error (Node × List Char × Nat)
  | 0, _, _ => .error .syntax
  | fuel + 1, cs, groups =>
    match parseAlternative fuel [] cs groups with
    | .error e => .error e
    | .ok (first, rest, groups') =>
      match rest with
      | '|' :: tail =>
        match parseDisjunction fuel tail groups' with
        | .error e => .error e
        | .ok (Node.alt others, rest', groups'') => .ok (.alt (first :: others), rest', groups'')
        | .ok (other, rest', groups'') => .ok (.alt [first, other], rest', groups'')
      | _ => .ok (first, rest, groups')

/-- Reads the terms of one alternative. -/
def parseAlternative : Nat → List Node → List Char → Nat → Except Error (Node × List Char × Nat)
  | 0, _, _, _ => .error .syntax
  | fuel + 1, acc, cs, groups =>
    match cs with
    | [] => .ok (.seq acc.reverse, cs, groups)
    | ')' :: _ => .ok (.seq acc.reverse, cs, groups)
    | '|' :: _ => .ok (.seq acc.reverse, cs, groups)
    | _ =>
      match parseTerm fuel cs groups with
      | .error e => .error e
      | .ok (term, rest, groups') => parseAlternative fuel (term :: acc) rest groups'

/-- Reads one term: an atom or an assertion, with its quantifier. -/
def parseTerm : Nat → List Char → Nat → Except Error (Node × List Char × Nat)
  | 0, _, _ => .error .syntax
  | fuel + 1, cs, groups =>
    match parseAtom fuel cs groups with
    | .error e => .error e
    | .ok (atom, quantifiable, rest, groups') =>
      match parseQuantifier rest with
      | .error e => .error e
      | .ok none => .ok (atom, rest, groups')
      | .ok (some (low, high, greedy, rest')) =>
        if quantifiable then .ok (.rep atom low high greedy, rest', groups') else .error .syntax

/-- Reads one atom or assertion; the flag tells whether a quantifier may follow. -/
def parseAtom : Nat → List Char → Nat → Except Error (Node × Bool × List Char × Nat)
  | 0, _, _ => .error .syntax
  | fuel + 1, cs, groups =>
    match cs with
    | [] => .error .syntax
    | '^' :: rest => .ok (.bol, false, rest, groups)
    | '$' :: rest => .ok (.eol, false, rest, groups)
    | '.' :: rest => .ok (.any, true, rest, groups)
    | '*' :: _ | '+' :: _ | '?' :: _ | '{' :: _ | '}' :: _ | ']' :: _ => .error .syntax
    | '\\' :: rest =>
      match parseEscape false rest with
      | .error e => .error e
      | .ok (.char c, tail) => .ok (.char c, true, tail, groups)
      | .ok (.set s, tail) => .ok (.cls s, true, tail, groups)
      | .ok (.boundary, tail) => .ok (.wordBoundary, false, tail, groups)
      | .ok (.notBoundary, tail) => .ok (.notWordBoundary, false, tail, groups)
    | '[' :: rest =>
      match parseClassBody fuel rest with
      | .error e => .error e
      | .ok (set, tail) => .ok (.cls set, true, tail, groups)
    | '(' :: '?' :: ':' :: rest => parseGroup fuel none rest groups
    | '(' :: '?' :: '<' :: '=' :: _ | '(' :: '?' :: '<' :: '!' :: _ | '(' :: '?' :: '=' :: _ | '(' :: '?' :: '!' :: _ =>
      .error .unsupported
    | '(' :: '?' :: '<' :: rest =>
      match rest with
      | first :: _ =>
        let name := rest.takeWhile isNamePart
        match rest.drop name.length with
        | '>' :: tail =>
          if isNameStart first then parseGroup fuel (some groups) tail (groups + 1) else .error .syntax
        | _ => .error .syntax
      | [] => .error .syntax
    | '(' :: '?' :: _ => .error .syntax
    | '(' :: rest => parseGroup fuel (some groups) rest (groups + 1)
    | c :: rest => .ok (.char c, true, rest, groups)

/-- Reads the inside of a group and its closing parenthesis. -/
def parseGroup : Nat → Option Nat → List Char → Nat → Except Error (Node × Bool × List Char × Nat)
  | 0, _, _, _ => .error .syntax
  | fuel + 1, index, cs, groups =>
    match parseDisjunction fuel cs groups with
    | .error e => .error e
    | .ok (inner, rest, groups') =>
      match rest with
      | ')' :: tail => .ok (.group index inner, true, tail, groups')
      | _ => .error .syntax
end

/-- Compiles a pattern in the unicode-sets mode of JavaScript regular expressions. -/
def Regex.compile (pattern : String) (ignoreCase : Bool := false) : Except Error Regex :=
  let cs := pattern.toList
  match parseDisjunction (4 * cs.length + 8) cs 0 with
  | .error e => .error e
  | .ok (node, [], groups) => .ok { node := node, groupCount := groups, ignoreCase := ignoreCase }
  | .ok (_, _ :: _, _) => .error .syntax

end Urllib.Regex
