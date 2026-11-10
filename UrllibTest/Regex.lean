import UrllibTest.Support
import Urllib.Regex.Parser

namespace UrllibTest.Regex

open Urllib.Regex

def run (pattern : String) (input : String) (ignoreCase : Bool := false) : Option (List (Option String)) :=
  match Regex.compile pattern ignoreCase with
  | .ok re => re.exec input
  | .error _ => none

def accepts (pattern : String) (input : String) (ignoreCase : Bool := false) : Bool :=
  (run pattern input ignoreCase).isSome

def errorOf (pattern : String) : Option Error :=
  match Regex.compile pattern with
  | .ok _ => none
  | .error e => some e

def checks : List UrllibTest.Check := [
  { name := "a literal matches itself", holds := accepts "abc" "abc" },
  { name := "a literal can match inside the input", holds := accepts "b" "abc" },
  { name := "an anchored literal must match the whole input", holds := accepts "^abc$" "abc" && !accepts "^abc$" "abcd" && !accepts "^abc$" "xabc" },
  { name := "the empty pattern matches the empty input", holds := accepts "" "" },
  { name := "a dot matches any code point but a line terminator", holds := accepts "^.$" "x" && accepts "^.$" "💩" && !accepts "^.$" "\n" && !accepts "^.$" "\r" },
  { name := "a star matches zero or more", holds := accepts "^a*$" "" && accepts "^a*$" "aaa" && !accepts "^a*$" "ab" },
  { name := "a plus matches one or more", holds := !accepts "^a+$" "" && accepts "^a+$" "aaa" },
  { name := "a question mark matches zero or one", holds := accepts "^a?$" "" && accepts "^a?$" "a" && !accepts "^a?$" "aa" },
  { name := "a counted repetition matches its range", holds := accepts "^a{2}$" "aa" && !accepts "^a{2}$" "a" && accepts "^a{2,}$" "aaaa" && accepts "^a{1,2}$" "aa" && !accepts "^a{1,2}$" "aaa" },
  { name := "a greedy repetition takes as much as it can and a lazy one as little", holds := run "^(a+)(a*)$" "aaa" == some [some "aaa", some ""] && run "^(a+?)(a*)$" "aaa" == some [some "a", some "aa"] },
  { name := "a lazy quantifier still matches when the rest needs more", holds := run "^(.+?)b$" "aab" == some [some "aa"] },
  { name := "an alternation matches either side", holds := accepts "^(?:a|b)$" "a" && accepts "^(?:a|b)$" "b" && !accepts "^(?:a|b)$" "c" },
  { name := "an alternation tries later alternatives after a failure", holds := run "^(a|ab)c$" "abc" == some [some "ab"] },
  { name := "three alternatives are all available", holds := accepts "^(?:x|y|z)$" "z" },
  { name := "capturing groups report their text in order", holds := run "^(a)(b)(c)$" "abc" == some [some "a", some "b", some "c"] },
  { name := "a group that does not take part is none", holds := run "^(a)|(b)$" "a" == some [some "a", none] },
  { name := "a non-capturing group adds no capture", holds := run "^(?:a)(b)$" "ab" == some [some "b"] },
  { name := "a named group is a capture", holds := run "^(?<x>a)$" "a" == some [some "a"] },
  { name := "a quantified group repeats", holds := accepts "^(?:ab)+$" "ababab" && !accepts "^(?:ab)+$" "aba" },
  { name := "a group inside a repetition keeps its last iteration", holds := run "^(a|b)+$" "abab" == some [some "b"] },
  { name := "an empty iteration does not loop forever", holds := accepts "^(?:a*)*$" "aaa" },
  { name := "a digit escape matches digits", holds := accepts "^\\d+$" "0123" && !accepts "^\\d+$" "12a" },
  { name := "a non-digit escape matches the rest", holds := accepts "^\\D+$" "abc" && !accepts "^\\D+$" "a1" },
  { name := "a word escape matches word characters", holds := accepts "^\\w+$" "ab_9" && !accepts "^\\w+$" "a-b" && accepts "^\\W$" "-" },
  { name := "a space escape matches white space", holds := accepts "^\\s$" " " && accepts "^\\s$" "\t" && accepts "^\\S$" "x" && !accepts "^\\S$" " " },
  { name := "control and character escapes match their code points", holds := accepts "^\\n\\r\\t\\f\\v\\0$" "\n\r\t\x0c\x0b\x00" },
  { name := "a hexadecimal escape matches its code point", holds := accepts "^\\x41$" "A" && accepts "^\\u0042$" "B" && accepts "^\\u{1F4A9}$" "💩" },
  { name := "a surrogate pair escape matches the supplementary code point", holds := accepts "^\\uD83D\\uDCA9$" "💩" },
  { name := "a control letter escape matches the control code point", holds := accepts "^\\cJ$" "\n" },
  { name := "an escaped syntax character matches itself", holds := accepts "^\\.\\*\\+\\?\\(\\)\\[\\]\\{\\}\\|\\/\\\\\\^\\$$" ".*+?()[]{}|/\\^$" },
  { name := "a word boundary sits between a word character and another", holds := accepts "\\bfoo\\b" "a foo b" && !accepts "\\bfoo\\b" "afoob" && accepts "a\\Bb" "ab" && !accepts "a\\Bb" "a b" },
  { name := "a character class matches its members", holds := accepts "^[abc]$" "b" && !accepts "^[abc]$" "d" },
  { name := "a character range matches its code points", holds := accepts "^[a-z]+$" "hello" && !accepts "^[a-z]+$" "Hello" },
  { name := "a negated class matches everything else", holds := accepts "^[^a-c]$" "d" && !accepts "^[^a-c]$" "b" && accepts "^[^]$" "x" },
  { name := "an empty class matches nothing", holds := !accepts "^[]$" "a" },
  { name := "class escapes work inside a class", holds := accepts "^[\\d_]+$" "1_2" && accepts "^[\\w\\-]*$" "a-" },
  { name := "a class may contain escaped syntax characters", holds := accepts "^[\\-\\]\\\\]+$" "-]\\" },
  { name := "a class subtraction removes the second set", holds := accepts "^[[a-z]--a]$" "b" && !accepts "^[[a-z]--a]$" "a" && !accepts "^[[a-z]--a]$" "A" },
  { name := "a class subtraction may chain", holds := !accepts "^[[a-z]--a--b]$" "b" && accepts "^[[a-z]--a--b]$" "c" },
  { name := "a class intersection keeps the common code points", holds := accepts "^[\\d&&[0-1]]$" "1" && !accepts "^[\\d&&[0-1]]$" "2" },
  { name := "a nested class joins the union", holds := accepts "^[a[0-9]]+$" "a1" },
  { name := "case-insensitive matching folds ASCII letters", holds := accepts "^abc$" "ABC" true && !accepts "^abc$" "ABC" false },
  { name := "case-insensitive classes fold ranges", holds := accepts "^[a-c]+$" "ABC" true && accepts "^[A-C]+$" "abc" true },
  { name := "a pattern may be searched from any position", holds := run "(\\d+)" "ab12cd" == some [some "12"] },
  { name := "a failing pattern gives none", holds := run "^a$" "b" == none },
  { name := "a nested quantifier on a group is accepted", holds := accepts "^(?:a{2}){2}$" "aaaa" },
  { name := "a lone closing parenthesis is a syntax error", holds := errorOf "a)" == some .syntax },
  { name := "an unclosed group is a syntax error", holds := errorOf "(a" == some .syntax },
  { name := "nothing to repeat is a syntax error", holds := errorOf "*a" == some .syntax && errorOf "+" == some .syntax && errorOf "?" == some .syntax },
  { name := "a lone brace is a syntax error", holds := errorOf "{" == some .syntax && errorOf "}" == some .syntax && errorOf "a{x}" == some .syntax },
  { name := "a lone closing bracket is a syntax error", holds := errorOf "]" == some .syntax },
  { name := "an unclosed class is a syntax error", holds := errorOf "[a" == some .syntax },
  { name := "a reversed range is a syntax error", holds := errorOf "[z-a]" == some .syntax && errorOf "a{3,2}" == some .syntax },
  { name := "an identity escape of an ordinary letter is a syntax error", holds := errorOf "\\m" == some .syntax && errorOf "\\H" == some .syntax },
  { name := "a group with an unknown flag is a syntax error", holds := errorOf "(?R)" == some .syntax },
  { name := "a trailing backslash is a syntax error", holds := errorOf "a\\" == some .syntax },
  { name := "an assertion cannot be quantified", holds := errorOf "^*" == some .syntax && errorOf "\\b+" == some .syntax },
  { name := "a bad hexadecimal escape is a syntax error", holds := errorOf "\\xZZ" == some .syntax && errorOf "\\u12" == some .syntax && errorOf "\\u{}" == some .syntax && errorOf "\\u{110000}" == some .syntax && errorOf "\\cJ1" == none && errorOf "\\c1" == some .syntax },
  { name := "a lone surrogate escape is a syntax error", holds := errorOf "\\uD83D" == some .syntax && errorOf "\\uDCA9" == some .syntax },
  { name := "a zero escape before a digit is a syntax error", holds := errorOf "\\00" == some .syntax },
  { name := "an unescaped syntax character in a class is a syntax error", holds := errorOf "[(]" == some .syntax && errorOf "[a/b]" == some .syntax },
  { name := "a reserved double punctuator in a class is a syntax error", holds := errorOf "[!!]" == some .syntax && errorOf "[a**]" == some .syntax },
  { name := "mixing union and subtraction in a class is a syntax error", holds := errorOf "[ab--c]" == some .syntax && errorOf "[a--b]" == none && accepts "^[a--b]$" "a" },
  { name := "mixing subtraction and intersection in a class is a syntax error", holds := errorOf "[[a-z]--a&&b]" == some .syntax && errorOf "[[a-z]&&a--b]" == some .syntax },
  { name := "a class with a range endpoint that is a set is a syntax error", holds := errorOf "[a-\\d]" == some .syntax && errorOf "[\\d-a]" == some .syntax },
  { name := "a boundary escape inside a class is a syntax error", holds := errorOf "[\\B]" == some .syntax },
  { name := "backspace is the meaning of a boundary escape inside a class", holds := accepts "^[\\b]$" "\x08" },
  { name := "a lookahead is unsupported", holds := errorOf "(?=a)" == some .unsupported && errorOf "(?!a)" == some .unsupported },
  { name := "a lookbehind is unsupported", holds := errorOf "(?<=a)" == some .unsupported && errorOf "(?<!a)" == some .unsupported },
  { name := "a backreference is unsupported", holds := errorOf "(a)\\1" == some .unsupported && errorOf "\\k<x>" == some .unsupported },
  { name := "a Unicode property escape is unsupported", holds := errorOf "\\p{L}" == some .unsupported && errorOf "\\P{L}" == some .unsupported },
  { name := "a bad group name is a syntax error", holds := errorOf "(?<1a>x)" == some .syntax && errorOf "(?<a" == some .syntax && errorOf "(?<" == some .syntax },
  { name := "a counted repetition may be lazy", holds := run "^(a{1,2}?)(a*)$" "aaa" == some [some "a", some "aa"] },
  { name := "an open ended counted repetition may be lazy", holds := run "^(a{1,}?)(a*)$" "aaa" == some [some "a", some "aa"] },
  { name := "every white space code point of JavaScript is a space", holds :=
      [9, 10, 11, 12, 13, 32, 0xA0, 0x1680, 0x2000, 0x2005, 0x200A, 0x2028, 0x2029, 0x202F, 0x205F, 0x3000, 0xFEFF].all
        fun n => isSpaceChar (Char.ofNat n) },
  { name := "the code points next to the white space ranges are not spaces", holds :=
      [8, 14, 31, 33, 0x9F, 0xA1, 0x167F, 0x1681, 0x1FFF, 0x200B, 0x2027, 0x202A, 0x202E, 0x2030, 0x205E, 0x2060, 0x2FFF, 0x3001, 0xFEFE, 0xFF00].all
        fun n => !isSpaceChar (Char.ofNat n) },
  { name := "line terminators are carriage return, line feed, and the two separators", holds :=
      [10, 13, 0x2028, 0x2029].all (fun n => isLineTerminator (Char.ofNat n)) &&
      [9, 11, 12, 14, 0x2027, 0x202A].all (fun n => !isLineTerminator (Char.ofNat n)) },
  { name := "a dot does not match the separators either", holds := !accepts "^.$" "\u2028" && !accepts "^.$" "\u2029" && accepts "^.$" "\u2027" },
  { name := "word characters are ASCII letters, digits, and underscore only", holds :=
      isWordChar 'a' && isWordChar 'Z' && isWordChar '0' && isWordChar '_' && !isWordChar '-' && !isWordChar 'é' },
  { name := "hexadecimal escapes accept every digit and reject the characters next to them", holds :=
      accepts "^\\x0f$" "\x0f" && accepts "^\\xAf$" "\u00af" && accepts "^\\xFa$" "\u00fa" && accepts "^\\x09$" "\t" &&
      errorOf "\\x/1" == some .syntax && errorOf "\\x:1" == some .syntax && errorOf "\\x@1" == some .syntax &&
      errorOf "\\xG1" == some .syntax && errorOf "\\x`1" == some .syntax && errorOf "\\xg1" == some .syntax },
  { name := "group names accept letters, dollar signs, underscores, and digits after the first", holds :=
      errorOf "(?<a1_$>x)" == none && errorOf "(?<$a>x)" == none && errorOf "(?<_a>x)" == none && errorOf "(?<A>x)" == none &&
      errorOf "(?<-a>x)" == some .syntax && errorOf "(?<a-b>x)" == some .syntax && errorOf "(?<0a>x)" == some .syntax },
  { name := "a quantifier on a nested class works", holds := accepts "^[[a-c]]{2}$" "ab" }
]

/-- Patterns that are valid, and some that are not, to be truncated and mutated by the robustness check. -/
def corpus : List String :=
  ["^abc$", "^(a)(b)(c)$", "^(?:a|b)+$", "^(?<x>a|bc)*?$", "^[a-z&&[^aeiou]]+$", "^[[a-z]--a--b]$", "^[\\d\\w\\s\\-]{1,3}?$",
   "\\bfoo\\B", "^\\x41\\u0042\\u{1F4A9}\\uD83D\\uDCA9\\cJ\\0$", "[^\\]\\\\]", "(?=a)(?!b)(?<=c)(?<!d)", "\\p{L}\\k<x>\\1",
   "[!!]", "[a-\\d]", "[\\B]", "a{2,3}", "a{3,2}", "(?<1x>a)", "(?R)", "[[a-z]&&a--b]", "[a&&[b]]", "\\u{110000}", "\\uD83D\\u0041"]

/-- Every prefix, every suffix, and every string with one code point removed. -/
def variants (s : String) : List String :=
  let cs := s.toList
  (List.range (cs.length + 1)).flatMap fun n =>
    [String.ofList (cs.take n), String.ofList (cs.drop n)] ++
      (if n < cs.length then [String.ofList (cs.take n ++ cs.drop (n + 1))] else [])

def robustnessChecks : List UrllibTest.Check := [
  { name := "compiling truncated and mutated patterns always terminates with a result", holds :=
      corpus.all fun s => (variants s).all fun v =>
        match Regex.compile v false with
        | .ok re => (re.exec "aAbc12 -x\n").isSome || (re.exec "aAbc12 -x\n").isNone
        | .error _ => true },
  { name := "a pattern that compiles keeps compiling when it is made case-insensitive", holds :=
      corpus.all fun s => ((Regex.compile s false).toOption.isSome) == ((Regex.compile s true).toOption.isSome) }
]

/-- info: [] -/
#guard_msgs in
#eval UrllibTest.failedChecks robustnessChecks

/-- info: [] -/
#guard_msgs in
#eval UrllibTest.failedChecks checks

end UrllibTest.Regex
