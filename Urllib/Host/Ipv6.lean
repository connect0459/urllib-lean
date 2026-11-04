import Urllib.Host.Ipv4

namespace Urllib.Host

/-- An IPv6 address as eight 16-bit pieces. -/
structure Ipv6 where
  /-- The pieces, most significant first. -/
  pieces : Vector UInt16 8
  deriving DecidableEq, Repr

/-- Reasons why the IPv6 parser rejects its input. -/
inductive Ipv6Error where
  /-- The input starts with a single colon. -/
  | invalidCompression
  /-- The input has more than eight pieces. -/
  | tooManyPieces
  /-- The input has more than one `::`. -/
  | multipleCompression
  /-- The input has an unexpected character or a misplaced colon. -/
  | invalidCodePoint
  /-- The input has fewer than eight pieces and no compression. -/
  | tooFewPieces
  /-- The embedded IPv4 part has an unexpected character or a leading zero. -/
  | ipv4InIpv6InvalidCodePoint
  /-- The embedded IPv4 part starts too late to fit in the address. -/
  | ipv4InIpv6TooManyPieces
  /-- A part of the embedded IPv4 address exceeds 255. -/
  | ipv4InIpv6OutOfRangePart
  /-- The embedded IPv4 address has fewer than four parts. -/
  | ipv4InIpv6TooFewParts
  deriving DecidableEq, Repr

namespace Ipv6

/-- The state of the IPv6 parser. -/
structure ParseState where
  /-- The pieces parsed so far. -/
  pieces : List Nat := List.replicate 8 0
  /-- The index of the next piece. -/
  pieceIndex : Nat := 0
  /-- The piece index at which a `::` compression was seen. -/
  compress : Option Nat := none

/-- Stores a piece at the current index and advances it. -/
def ParseState.setPiece (st : ParseState) (value : Nat) : ParseState :=
  { st with pieces := st.pieces.set st.pieceIndex value, pieceIndex := st.pieceIndex + 1 }

/-- Reads at most `budget` hexadecimal digits, returning their value, their count, and the remaining characters. -/
def readHex : Nat → Nat → Nat → List Char → Nat × Nat × List Char
  | 0, acc, len, chars => (acc, len, chars)
  | _ + 1, acc, len, [] => (acc, len, [])
  | budget + 1, acc, len, c :: rest =>
    match Ipv4.digitValue? 16 c with
    | some digit => readHex budget (acc * 16 + digit) (len + 1) rest
    | none => (acc, len, c :: rest)

/-- Reads one decimal part of an embedded IPv4 address, rejecting leading zeros and values above 255. -/
def readDecimalPiece : Option Nat → List Char → Except Ipv6Error (Nat × List Char)
  | piece, c :: rest =>
    if c.isDigit then
      let digit := c.toNat - 0x30
      match piece with
      | none => readDecimalPiece (some digit) rest
      | some 0 => .error .ipv4InIpv6InvalidCodePoint
      | some p =>
        if p * 10 + digit > 255 then .error .ipv4InIpv6OutOfRangePart
        else readDecimalPiece (some (p * 10 + digit)) rest
    else
      .ok (piece.getD 0, c :: rest)
  | piece, [] => .ok (piece.getD 0, [])

/-- Reads the dotted decimal part of an embedded IPv4 address into the pieces, returning the state and the number of parts seen. -/
def readIpv4Parts : Nat → ParseState → Nat → List Char →
    Except Ipv6Error (ParseState × Nat)
  | _, st, seen, [] => .ok (st, seen)
  | 0, _, _, _ => .error .ipv4InIpv6InvalidCodePoint
  | fuel + 1, st, seen, chars => do
    let chars ←
      if seen > 0 then
        match chars with
        | '.' :: rest => if seen < 4 then pure rest else throw .ipv4InIpv6InvalidCodePoint
        | _ => throw .ipv4InIpv6InvalidCodePoint
      else pure chars
    match chars with
    | c :: _ =>
      if c.isDigit then
        let (piece, rest) ← readDecimalPiece none chars
        let merged := st.pieces[st.pieceIndex]! * 0x100 + piece
        let seen := seen + 1
        let st :=
          { st with
            pieces := st.pieces.set st.pieceIndex merged
            pieceIndex := if seen = 2 ∨ seen = 4 then st.pieceIndex + 1 else st.pieceIndex }
        readIpv4Parts fuel st seen rest
      else throw .ipv4InIpv6InvalidCodePoint
    | [] => throw .ipv4InIpv6InvalidCodePoint

/-- The main loop of the IPv6 parser; `fuel` bounds the iterations. -/
def parseLoop : Nat → ParseState → List Char → Except Ipv6Error ParseState
  | _, st, [] => .ok st
  | 0, _, _ => .error .invalidCodePoint
  | fuel + 1, st, chars@(c :: rest) =>
    if st.pieceIndex = 8 then .error .tooManyPieces
    else if c = ':' then
      if st.compress.isSome then .error .multipleCompression
      else
        parseLoop fuel
          { st with pieceIndex := st.pieceIndex + 1, compress := some (st.pieceIndex + 1) } rest
    else
      match readHex 4 0 0 chars with
      | (_, length, '.' :: _) =>
        if length = 0 then .error .ipv4InIpv6InvalidCodePoint
        else if st.pieceIndex > 6 then .error .ipv4InIpv6TooManyPieces
        else do
          let (st, seen) ← readIpv4Parts chars.length st 0 chars
          if seen ≠ 4 then throw .ipv4InIpv6TooFewParts
          return st
      | (value, _, ':' :: afterColon) =>
        if afterColon.isEmpty then .error .invalidCodePoint
        else parseLoop fuel (st.setPiece value) afterColon
      | (value, _, []) => .ok (st.setPiece value)
      | _ => .error .invalidCodePoint

/-- Moves the pieces after the compression point to the end and fills the gap with zeros. -/
def expandCompression (pieces : List Nat) (compress swaps : Nat) : List Nat :=
  pieces.take compress ++ List.replicate (8 - compress - swaps) 0 ++
    (pieces.drop compress).take swaps

/-- Builds an address from the first eight entries of a piece list. -/
def ofPieces (pieces : List Nat) : Ipv6 :=
  ⟨Vector.ofFn fun i => UInt16.ofNat pieces[i.val]!⟩

/-- Expands the compression, or checks that all eight pieces are present. -/
def finishParse (st : ParseState) : Except Ipv6Error Ipv6 :=
  match st.compress with
  | some compress =>
    .ok (ofPieces (expandCompression st.pieces compress (st.pieceIndex - compress)))
  | none =>
    if st.pieceIndex ≠ 8 then .error .tooFewPieces else .ok (ofPieces st.pieces)

/-- The IPv6 parser on characters. -/
def parseChars (input : List Char) : Except Ipv6Error Ipv6 :=
  match input with
  | ':' :: ':' :: rest =>
    parseLoop (rest.length + 1) { pieceIndex := 1, compress := some 1 } rest >>= finishParse
  | ':' :: _ => .error .invalidCompression
  | chars => parseLoop (chars.length + 1) {} chars >>= finishParse

/-- The IPv6 parser of the URL Standard. -/
def parse (input : String) : Except Ipv6Error Ipv6 :=
  parseChars input.toList

/-- Scans the pieces for the first longest run of zeros, returning its start and length. -/
def findCompressLoop : List Nat → Nat → Nat → Nat → Nat → Nat → Nat × Nat
  | [], _, _, _, bestStart, bestLength => (bestStart, bestLength)
  | piece :: rest, index, runStart, runLength, bestStart, bestLength =>
    if piece = 0 then
      let runStart := if runLength = 0 then index else runStart
      let runLength := runLength + 1
      if runLength > bestLength then
        findCompressLoop rest (index + 1) runStart runLength runStart runLength
      else
        findCompressLoop rest (index + 1) runStart runLength bestStart bestLength
    else
      findCompressLoop rest (index + 1) 0 0 bestStart bestLength

/-- The start of the first longest run of zero pieces, when that run is longer than one piece. -/
def findCompress (pieces : List Nat) : Option Nat :=
  let (bestStart, bestLength) := findCompressLoop pieces 0 0 0 0 0
  if bestLength > 1 then some bestStart else none

/-- The lowercase hexadecimal digit for `d`, which must be below 16. -/
def hexChar (d : Nat) : Char :=
  if d < 10 then Char.ofNat (0x30 + d) else Char.ofNat (0x61 + d - 10)

/-- The lowercase hexadecimal digits of a piece without leading zeros. -/
def hexDigits (p : Nat) : List Char :=
  if p < 16 then [hexChar p] else hexDigits (p / 16) ++ [hexChar (p % 16)]
termination_by p
decreasing_by omega

/-- Prints the pieces from `index`, writing the compression as `::` and skipping the zeros it covers. -/
def printFrom (compress : Option Nat) : Nat → Bool → List Nat → List Char
  | _, _, [] => []
  | index, ignoreZeros, piece :: rest =>
    if ignoreZeros && piece = 0 then
      printFrom compress (index + 1) ignoreZeros rest
    else if compress = some index then
      (if index = 0 then [':', ':'] else [':']) ++ printFrom compress (index + 1) true rest
    else
      hexDigits piece ++ (if index ≠ 7 then [':'] else []) ++
        printFrom compress (index + 1) false rest

/-- The compressed lowercase form of an address, without brackets. -/
def serialize (address : Ipv6) : String :=
  let pieces := address.pieces.toList.map UInt16.toNat
  String.ofList (printFrom (findCompress pieces) 0 false pieces)

end Ipv6

end Urllib.Host
