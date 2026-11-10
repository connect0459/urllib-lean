import Urllib.UrlPattern.Tokenizer

namespace Urllib.UrlPattern

/-- The kinds of part of a parsed pattern string. -/
inductive PartType where
  /-- Fixed text. -/
  | fixedText
  /-- A group with a custom regular expression. -/
  | regexp
  /-- A group that matches up to the next delimiter. -/
  | segmentWildcard
  /-- A group that matches everything. -/
  | fullWildcard
  deriving DecidableEq, Repr

/-- The modifier of a part. -/
inductive Modifier where
  /-- No modifier. -/
  | none
  /-- `?`. -/
  | optional
  /-- `*`. -/
  | zeroOrMore
  /-- `+`. -/
  | oneOrMore
  deriving DecidableEq, Repr

/-- A part of a parsed pattern string. -/
structure Part where
  /-- The kind of part. -/
  type : PartType
  /-- The fixed text, or the regular expression of a `regexp` part. -/
  value : String
  /-- The modifier. -/
  modifier : Modifier
  /-- The name of the group; empty for fixed text. -/
  name : String
  /-- The fixed text before the group. -/
  leading : String
  /-- The fixed text after the group. -/
  trailing : String
  deriving DecidableEq, Repr

/-- The options of a component: the delimiter and the prefix code point, each one ASCII code point or empty, and whether the matching ignores case. -/
structure Options where
  /-- The segment separator. -/
  delimiter : String
  /-- The code point that becomes the prefix of a group that follows it. -/
  prefixCodePoint : String
  /-- Whether the matching ignores case. -/
  ignoreCase : Bool
  deriving DecidableEq, Repr

/-- The options of every component but the hostname and the pathname. -/
def Options.default : Options := { delimiter := "", prefixCodePoint := "", ignoreCase := false }

/-- The options of the hostname. -/
def Options.hostname : Options := { delimiter := ".", prefixCodePoint := "", ignoreCase := false }

/-- The options of a pathname of a URL with a special scheme. -/
def Options.pathname : Options := { delimiter := "/", prefixCodePoint := "/", ignoreCase := false }

/-- The regular expression of a full wildcard. -/
def fullWildcardRegexp : String := ".*"

/-- Escapes the code points that are special in a regular expression. -/
def escapeRegexp (input : String) : String :=
  String.join (input.toList.map fun c =>
    if ".+*?^${}()[]|/\\".toList.contains c then "\\" ++ String.singleton c else String.singleton c)

/-- Escapes the code points that are special in a pattern string. -/
def escapePattern (input : String) : String :=
  String.join (input.toList.map fun c =>
    if "+*?:{}()\\".toList.contains c then "\\" ++ String.singleton c else String.singleton c)

/-- The regular expression of a segment wildcard. -/
def segmentWildcardRegexp (options : Options) : String :=
  "[^" ++ escapeRegexp options.delimiter ++ "]+?"

/-- The state of the pattern parser. -/
structure ParserState where
  /-- The tokens. -/
  tokens : Array Token
  /-- The index of the next token. -/
  index : Nat
  /-- The parts so far, last first. -/
  parts : List Part
  /-- The fixed text that is not yet a part. -/
  pending : String
  /-- The number for the next unnamed group. -/
  nextNumeric : Nat

/-- Consumes the next token if it has the type. -/
def tryConsume (st : ParserState) (type : TokenType) : Option Token × ParserState :=
  match st.tokens[st.index]? with
  | some token =>
    if token.type == type then (some token, { st with index := st.index + 1 }) else (none, st)
  | none => (none, st)

/-- Consumes a modifier token: `?`, `+`, or an asterisk. -/
def tryConsumeModifier (st : ParserState) : Option Token × ParserState :=
  match tryConsume st .otherModifier with
  | (some token, st') => (some token, st')
  | (none, st') => tryConsume st' .asterisk

/-- Consumes a regular expression token, or an asterisk when there is no name token. -/
def tryConsumeRegexpOrWildcard (st : ParserState) (nameToken : Option Token) : Option Token × ParserState :=
  match tryConsume st .regexp with
  | (some token, st') => (some token, st')
  | (none, st') => if nameToken.isNone then tryConsume st' .asterisk else (none, st')

/-- Consumes a token that must be there. -/
def consumeRequired (st : ParserState) (type : TokenType) : Except Error ParserState :=
  match tryConsume st type with
  | (some _, st') => .ok st'
  | (none, _) => .error .pattern

/-- Consumes the run of `char` and `escaped-char` tokens as text. -/
def consumeText (st : ParserState) (fuel : Nat) : String × ParserState :=
  match fuel with
  | 0 => ("", st)
  | fuel + 1 =>
    let (token, st') :=
      match tryConsume st .char with
      | (some t, s) => (some t, s)
      | (none, s) => tryConsume s .escapedChar
    match token with
    | none => ("", st)
    | some t =>
      let (rest, st'') := consumeText st' fuel
      (t.value ++ rest, st'')

/-- Turns the pending fixed text into a part. -/
def maybeAddFixedPart (encode : String → Except Error String) (st : ParserState) : Except Error ParserState :=
  if st.pending.isEmpty then .ok st
  else
    match encode st.pending with
    | .error e => .error e
    | .ok encoded =>
      .ok { st with pending := "",
                    parts := { type := .fixedText, value := encoded, modifier := .none, name := "", leading := "", trailing := "" } :: st.parts }

/-- The modifier that a token stands for. -/
def modifierOf (token : Option Token) : Modifier :=
  match token with
  | none => .none
  | some t => if t.value == "?" then .optional else if t.value == "*" then .zeroOrMore else if t.value == "+" then .oneOrMore else .none

/-- Adds a part for a group with its prefix, suffix and modifier. -/
def addPart (options : Options) (encode : String → Except Error String) (st : ParserState) (prefixText : String)
    (nameToken regexpToken : Option Token) (suffixText : String) (modifierToken : Option Token) : Except Error ParserState :=
  let modifier := modifierOf modifierToken
  if nameToken.isNone && regexpToken.isNone && modifier == .none then
    .ok { st with pending := st.pending ++ prefixText }
  else
    match maybeAddFixedPart encode st with
    | .error e => .error e
    | .ok st' =>
      if nameToken.isNone && regexpToken.isNone then
        if prefixText.isEmpty then .ok st'
        else
          match encode prefixText with
          | .error e => .error e
          | .ok encoded =>
            .ok { st' with parts := { type := .fixedText, value := encoded, modifier := modifier, name := "", leading := "", trailing := "" } :: st'.parts }
      else
        let segment := segmentWildcardRegexp options
        let regexpValue :=
          match regexpToken with
          | none => segment
          | some t => if t.type == .asterisk then fullWildcardRegexp else t.value
        let (type, value) :=
          if regexpValue == segment then (PartType.segmentWildcard, "")
          else if regexpValue == fullWildcardRegexp then (PartType.fullWildcard, "")
          else (PartType.regexp, regexpValue)
        let (name, nextNumeric) :=
          match nameToken with
          | some t => (t.value, st'.nextNumeric)
          | none => (toString st'.nextNumeric, st'.nextNumeric + 1)
        if st'.parts.any (fun p => p.name == name) then .error .pattern
        else
          match encode prefixText, encode suffixText with
          | .ok encodedPrefix, .ok encodedSuffix =>
            .ok { st' with nextNumeric := nextNumeric,
                           parts := { type := type, value := value, modifier := modifier, name := name,
                                      leading := encodedPrefix, trailing := encodedSuffix } :: st'.parts }
          | .error e, _ => .error e
          | _, .error e => .error e

/-- The loop of the pattern parser. -/
def parseLoop (options : Options) (encode : String → Except Error String) :
    Nat → ParserState → Except Error (List Part)
  | 0, _ => .error .pattern
  | fuel + 1, st =>
    let (charToken, st) := tryConsume st .char
    let (nameToken, st) := tryConsume st .name
    let (regexpToken, st) := tryConsumeRegexpOrWildcard st nameToken
    if nameToken.isSome || regexpToken.isSome then
      let prefix0 := (charToken.map (·.value)).getD ""
      let (prefixText, st) :=
        if !prefix0.isEmpty && prefix0 != options.prefixCodePoint then ("", { st with pending := st.pending ++ prefix0 })
        else (prefix0, st)
      match maybeAddFixedPart encode st with
      | .error e => .error e
      | .ok st =>
        let (modifierToken, st) := tryConsumeModifier st
        match addPart options encode st prefixText nameToken regexpToken "" modifierToken with
        | .error e => .error e
        | .ok st => parseLoop options encode fuel st
    else
      let (fixedToken, st) :=
        match charToken with
        | some t => (some t, st)
        | none => tryConsume st .escapedChar
      match fixedToken with
      | some t => parseLoop options encode fuel { st with pending := st.pending ++ t.value }
      | none =>
        let (openToken, st) := tryConsume st .groupOpen
        if openToken.isSome then
          let (prefixText, st) := consumeText st (st.tokens.size + 1)
          let (nameToken, st) := tryConsume st .name
          let (regexpToken, st) := tryConsumeRegexpOrWildcard st nameToken
          let (suffixText, st) := consumeText st (st.tokens.size + 1)
          match consumeRequired st .groupClose with
          | .error e => .error e
          | .ok st =>
            let (modifierToken, st) := tryConsumeModifier st
            match addPart options encode st prefixText nameToken regexpToken suffixText modifierToken with
            | .error e => .error e
            | .ok st => parseLoop options encode fuel st
        else
          match maybeAddFixedPart encode st with
          | .error e => .error e
          | .ok st =>
            match consumeRequired st .endOfInput with
            | .error e => .error e
            | .ok st => .ok st.parts.reverse

/-- Parses a pattern string into parts, encoding every fixed text with `encode`. -/
def parsePattern (input : String) (options : Options) (encode : String → Except Error String) :
    Except Error (List Part) :=
  match tokenize input .strict with
  | .error e => .error e
  | .ok tokens =>
    parseLoop options encode (tokens.length + 2)
      { tokens := tokens.toArray, index := 0, parts := [], pending := "", nextNumeric := 0 }

/-- The text of a modifier in a pattern or a regular expression. -/
def modifierText (modifier : Modifier) : String :=
  match modifier with
  | .zeroOrMore => "*"
  | .optional => "?"
  | .oneOrMore => "+"
  | .none => ""

/-- The regular expression of a part, and its group name if it has one. -/
def partRegexp (options : Options) (part : Part) : String :=
  let regexpValue :=
    match part.type with
    | .segmentWildcard => segmentWildcardRegexp options
    | .fullWildcard => fullWildcardRegexp
    | _ => part.value
  if part.leading.isEmpty && part.trailing.isEmpty then
    if part.modifier == .none || part.modifier == .optional then
      "(" ++ regexpValue ++ ")" ++ modifierText part.modifier
    else "((?:" ++ regexpValue ++ ")" ++ modifierText part.modifier ++ ")"
  else if part.modifier == .none || part.modifier == .optional then
    "(?:" ++ escapeRegexp part.leading ++ "(" ++ regexpValue ++ ")" ++ escapeRegexp part.trailing ++ ")" ++ modifierText part.modifier
  else
    "(?:" ++ escapeRegexp part.leading ++ "((?:" ++ regexpValue ++ ")(?:" ++ escapeRegexp part.trailing ++
      escapeRegexp part.leading ++ "(?:" ++ regexpValue ++ "))*)" ++ escapeRegexp part.trailing ++ ")" ++
      (if part.modifier == .zeroOrMore then "?" else "")

/-- Generates the regular expression string and the group names of a part list. -/
def generateRegexp (parts : List Part) (options : Options) : String × List String :=
  let body := parts.map fun part =>
    match part.type with
    | .fixedText =>
      if part.modifier == .none then escapeRegexp part.value
      else "(?:" ++ escapeRegexp part.value ++ ")" ++ modifierText part.modifier
    | _ => partRegexp options part
  ("^" ++ String.join body ++ "$", (parts.filter fun p => p.type != .fixedText).map (·.name))

/-- Whether the first code point of a pattern text can continue a name. -/
def startsWithNamePart (text : String) : Bool :=
  match text.toList with
  | c :: _ => isNamePart c
  | [] => false

/-- Whether a name does not begin with a digit, which makes it a custom name. -/
def isCustomName (name : String) : Bool :=
  match name.toList with
  | c :: _ => !c.isDigit
  | [] => false

/-- Generates the pattern string of a part list. -/
def generatePattern (parts : List Part) (options : Options) : String :=
  let arr := parts.toArray
  let step (index : Nat) (part : Part) : String :=
    let previous := if index > 0 then arr[index - 1]? else none
    let next := arr[index + 1]?
    match part.type with
    | .fixedText =>
      if part.modifier == .none then escapePattern part.value
      else "{" ++ escapePattern part.value ++ "}" ++ modifierText part.modifier
    | _ =>
      let customName := isCustomName part.name
      let needsGrouping0 := !part.trailing.isEmpty || (!part.leading.isEmpty && part.leading != options.prefixCodePoint)
      let needsGrouping1 :=
        if !needsGrouping0 && customName && part.type == .segmentWildcard && part.modifier == .none then
          match next with
          | some n =>
            if n.leading.isEmpty && n.trailing.isEmpty then
              if n.type == .fixedText then startsWithNamePart n.value else !isCustomName n.name
            else false
          | none => false
        else needsGrouping0
      let needsGrouping :=
        if !needsGrouping1 && part.leading.isEmpty then
          match previous with
          | some p => p.type == .fixedText && (p.value.toList.getLast?.map String.singleton) == some options.prefixCodePoint &&
              !options.prefixCodePoint.isEmpty
          | none => false
        else needsGrouping1
      let core :=
        (if customName then ":" ++ part.name else "") ++
        (match part.type with
          | .regexp => "(" ++ part.value ++ ")"
          | .segmentWildcard => if customName then "" else "(" ++ segmentWildcardRegexp options ++ ")"
          | _ =>
            if !customName && (previous.isNone || previous.any (·.type == .fixedText) ||
                previous.any (·.modifier != .none) || needsGrouping || !part.leading.isEmpty) then "*"
            else "(" ++ fullWildcardRegexp ++ ")")
      let escapeSuffix :=
        part.type == .segmentWildcard && customName && !part.trailing.isEmpty && startsWithNamePart part.trailing
      (if needsGrouping then "{" else "") ++ escapePattern part.leading ++ core ++
        (if escapeSuffix then "\\" else "") ++ escapePattern part.trailing ++
        (if needsGrouping then "}" else "") ++ modifierText part.modifier
  String.join (arr.toList.mapIdx step)

end Urllib.UrlPattern
