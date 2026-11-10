import Urllib.UrlPattern.Init
import Urllib.UrlPattern.Component

namespace Urllib.UrlPattern

/-- The states of the constructor string parser. -/
inductive CtorState where
  /-- The initial state. -/
  | init
  /-- Reading the protocol. -/
  | protocol
  /-- Reading the authority. -/
  | authority
  /-- Reading the username. -/
  | username
  /-- Reading the password. -/
  | password
  /-- Reading the hostname. -/
  | hostname
  /-- Reading the port. -/
  | port
  /-- Reading the pathname. -/
  | pathname
  /-- Reading the search. -/
  | search
  /-- Reading the hash. -/
  | hash
  /-- Finished. -/
  | done
  deriving DecidableEq, Repr

/-- The constructor string parser. -/
structure Ctor where
  /-- The input as code points. -/
  input : Array Char
  /-- The tokens. -/
  tokens : Array Token
  /-- The result so far. -/
  result : Init
  /-- The token index where the current component starts. -/
  componentStart : Nat
  /-- The current token index. -/
  tokenIndex : Nat
  /-- The amount that the token index grows after a step. -/
  tokenIncrement : Nat
  /-- The depth of `{` groups. -/
  groupDepth : Nat
  /-- The depth of IPv6 brackets in the hostname. -/
  ipv6Depth : Nat
  /-- Whether the protocol matches a special scheme. -/
  protocolMatchesSpecial : Bool
  /-- The state. -/
  state : CtorState

namespace Ctor

/-- The token at an index, or the last token (the end) when the index is past the list. -/
def safeToken (p : Ctor) (index : Nat) : Token :=
  match p.tokens[index]? with
  | some t => t
  | none => (p.tokens.back?).getD { type := .endOfInput, index := 0, value := "" }

/-- Whether the token at the index is a non-special pattern character with the given value. -/
def isNonSpecialPatternChar (p : Ctor) (index : Nat) (value : String) : Bool :=
  let t := p.safeToken index
  t.value == value && (t.type == .char || t.type == .escapedChar || t.type == .invalidChar)

/-- The input between the start of the component and the current token. -/
def makeComponentString (p : Ctor) : String :=
  let startIndex := (p.safeToken p.componentStart).index
  let endIndex := (p.safeToken p.tokenIndex).index
  substring p.input startIndex (endIndex - startIndex)

/-- Starts a new state: stores the finished component and fills the components that the new state skips. -/
def changeState (p : Ctor) (newState : CtorState) (skip : Nat) : Ctor :=
  let result0 :=
    if p.state != .init && p.state != .authority && p.state != .done then
      match p.state with
      | .protocol => p.result.set .protocol (some p.makeComponentString)
      | .username => p.result.set .username (some p.makeComponentString)
      | .password => p.result.set .password (some p.makeComponentString)
      | .hostname => p.result.set .hostname (some p.makeComponentString)
      | .port => p.result.set .port (some p.makeComponentString)
      | .pathname => p.result.set .pathname (some p.makeComponentString)
      | .search => p.result.set .search (some p.makeComponentString)
      | .hash => p.result.set .hash (some p.makeComponentString)
      | _ => p.result
    else p.result
  let result1 :=
    if p.state != .init && newState != .done then
      let r1 :=
        if (p.state == .protocol || p.state == .authority || p.state == .username || p.state == .password) &&
            (newState == .port || newState == .pathname || newState == .search || newState == .hash) &&
            result0.hostname.isNone then
          { result0 with hostname := some "" }
        else result0
      let r2 :=
        if (p.state == .protocol || p.state == .authority || p.state == .username || p.state == .password ||
            p.state == .hostname || p.state == .port) && (newState == .search || newState == .hash) &&
            r1.pathname.isNone then
          { r1 with pathname := some (if p.protocolMatchesSpecial then "/" else "") }
        else r1
      if (p.state == .protocol || p.state == .authority || p.state == .username || p.state == .password ||
          p.state == .hostname || p.state == .port || p.state == .pathname) && newState == .hash &&
          r2.search.isNone then
        { r2 with search := some "" }
      else r2
    else result0
  let index := p.tokenIndex + skip
  { p with result := result1, state := newState, tokenIndex := index, componentStart := index, tokenIncrement := 0 }

/-- Moves the token index back to the start of the component. -/
def rewind (p : Ctor) : Ctor :=
  { p with tokenIndex := p.componentStart, tokenIncrement := 0 }

/-- Moves back to the start of the component and switches state. -/
def rewindAndSetState (p : Ctor) (state : CtorState) : Ctor :=
  { p.rewind with state := state }

/-- Whether the current token is a search prefix. -/
def isSearchPrefix (p : Ctor) : Bool :=
  if p.isNonSpecialPatternChar p.tokenIndex "?" then true
  else if (p.safeToken p.tokenIndex).value != "?" then false
  else
    match p.tokenIndex with
    | 0 => true
    | previous + 1 =>
      let t := p.safeToken previous
      !(t.type == .name || t.type == .regexp || t.type == .groupClose || t.type == .asterisk)

/-- Decides whether the protocol matches a special scheme by compiling it. -/
def computeProtocolMatchesSpecial (p : Ctor) : Except Error Ctor := do
  let component ← compileComponent p.makeComponentString canonicalizeProtocol Options.default
  return { p with protocolMatchesSpecial := component.matchesSpecialScheme }

end Ctor

/-- One iteration of the constructor string parser on a token that is not the end. -/
def ctorStep (p : Ctor) : Except Error Ctor := do
  let token := p.safeToken p.tokenIndex
  if token.type == .groupOpen then
    return { p with groupDepth := p.groupDepth + 1, tokenIndex := p.tokenIndex + p.tokenIncrement }
  let p1 ←
    if p.groupDepth > 0 then
      if token.type == .groupClose then pure (some { p with groupDepth := p.groupDepth - 1 })
      else pure none
    else pure (some p)
  match p1 with
  | none => return { p with tokenIndex := p.tokenIndex + p.tokenIncrement }
  | some p =>
    let p ←
      match p.state with
      | .init =>
        pure (if p.isNonSpecialPatternChar p.tokenIndex ":" then p.rewindAndSetState .protocol else p)
      | .protocol =>
        if p.isNonSpecialPatternChar p.tokenIndex ":" then
          let p ← p.computeProtocolMatchesSpecial
          let authoritySlashes := p.isNonSpecialPatternChar (p.tokenIndex + 1) "/" && p.isNonSpecialPatternChar (p.tokenIndex + 2) "/"
          if authoritySlashes then pure (p.changeState .authority 3)
          else if p.protocolMatchesSpecial then pure (p.changeState .authority 1)
          else pure (p.changeState .pathname 1)
        else pure p
      | .authority =>
        if p.isNonSpecialPatternChar p.tokenIndex "@" then pure (p.rewindAndSetState .username)
        else if p.isNonSpecialPatternChar p.tokenIndex "/" || p.isSearchPrefix || p.isNonSpecialPatternChar p.tokenIndex "#" then
          pure (p.rewindAndSetState .hostname)
        else pure p
      | .username =>
        if p.isNonSpecialPatternChar p.tokenIndex ":" then pure (p.changeState .password 1)
        else if p.isNonSpecialPatternChar p.tokenIndex "@" then pure (p.changeState .hostname 1)
        else pure p
      | .password =>
        if p.isNonSpecialPatternChar p.tokenIndex "@" then pure (p.changeState .hostname 1) else pure p
      | .hostname =>
        if p.isNonSpecialPatternChar p.tokenIndex "[" then pure { p with ipv6Depth := p.ipv6Depth + 1 }
        else if p.isNonSpecialPatternChar p.tokenIndex "]" then pure { p with ipv6Depth := p.ipv6Depth - 1 }
        else if p.isNonSpecialPatternChar p.tokenIndex ":" && p.ipv6Depth == 0 then pure (p.changeState .port 1)
        else if p.isNonSpecialPatternChar p.tokenIndex "/" then pure (p.changeState .pathname 0)
        else if p.isSearchPrefix then pure (p.changeState .search 1)
        else if p.isNonSpecialPatternChar p.tokenIndex "#" then pure (p.changeState .hash 1)
        else pure p
      | .port =>
        if p.isNonSpecialPatternChar p.tokenIndex "/" then pure (p.changeState .pathname 0)
        else if p.isSearchPrefix then pure (p.changeState .search 1)
        else if p.isNonSpecialPatternChar p.tokenIndex "#" then pure (p.changeState .hash 1)
        else pure p
      | .pathname =>
        if p.isSearchPrefix then pure (p.changeState .search 1)
        else if p.isNonSpecialPatternChar p.tokenIndex "#" then pure (p.changeState .hash 1)
        else pure p
      | .search =>
        if p.isNonSpecialPatternChar p.tokenIndex "#" then pure (p.changeState .hash 1) else pure p
      | .hash => pure p
      | .done => pure p
    return { p with tokenIndex := p.tokenIndex + p.tokenIncrement }

/-- The loop of the constructor string parser. -/
def ctorLoop : Nat → Ctor → Except Error Ctor
  | 0, p => .ok p
  | fuel + 1, p =>
    if p.tokenIndex < p.tokens.size then
      let p := { p with tokenIncrement := 1 }
      let token := p.safeToken p.tokenIndex
      if token.type == .endOfInput then
        match p.state with
        | .init =>
          let p := p.rewind
          let p :=
            if p.isNonSpecialPatternChar p.tokenIndex "#" then p.changeState .hash 1
            else if p.isSearchPrefix then p.changeState .search 1
            else p.changeState .pathname 0
          ctorLoop fuel { p with tokenIndex := p.tokenIndex + p.tokenIncrement }
        | .authority =>
          let p := p.rewindAndSetState .hostname
          ctorLoop fuel { p with tokenIndex := p.tokenIndex + p.tokenIncrement }
        | _ => .ok (p.changeState .done 0)
      else
        match ctorStep p with
        | .error e => .error e
        | .ok p' => ctorLoop fuel p'
    else .ok p

/-- Parses a constructor string into a URLPatternInit. -/
def parseConstructorString (input : String) : Except Error Init := do
  let tokens ← tokenize input .lenient
  let p : Ctor :=
    { input := input.toList.toArray, tokens := tokens.toArray, result := {}, componentStart := 0, tokenIndex := 0,
      tokenIncrement := 1, groupDepth := 0, ipv6Depth := 0, protocolMatchesSpecial := false, state := .init }
  let p ← ctorLoop (8 * (tokens.length + 2)) p
  let result := if p.result.hostname.isSome && p.result.port.isNone then { p.result with port := some "" } else p.result
  return result

end Urllib.UrlPattern
