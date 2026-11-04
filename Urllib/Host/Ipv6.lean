import Urllib.Host.Ipv4

namespace Urllib.Host

structure Ipv6 where
  pieces : Vector UInt16 8
  deriving DecidableEq, Repr

inductive Ipv6Error where
  | invalidCompression
  | tooManyPieces
  | multipleCompression
  | invalidCodePoint
  | tooFewPieces
  | ipv4InIpv6InvalidCodePoint
  | ipv4InIpv6TooManyPieces
  | ipv4InIpv6OutOfRangePart
  | ipv4InIpv6TooFewParts
  deriving DecidableEq, Repr

namespace Ipv6

structure ParseState where
  pieces : Array Nat := Array.replicate 8 0
  pieceIndex : Nat := 0
  compress : Option Nat := none

def ParseState.setPiece (st : ParseState) (value : Nat) : ParseState :=
  { st with pieces := st.pieces.set! st.pieceIndex value, pieceIndex := st.pieceIndex + 1 }

def readHex : Nat → Nat → Nat → List Char → Nat × Nat × List Char
  | 0, acc, len, chars => (acc, len, chars)
  | _ + 1, acc, len, [] => (acc, len, [])
  | budget + 1, acc, len, c :: rest =>
    match Ipv4.digitValue? 16 c with
    | some digit => readHex budget (acc * 16 + digit) (len + 1) rest
    | none => (acc, len, c :: rest)

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
            pieces := st.pieces.set! st.pieceIndex merged
            pieceIndex := if seen = 2 ∨ seen = 4 then st.pieceIndex + 1 else st.pieceIndex }
        readIpv4Parts fuel st seen rest
      else throw .ipv4InIpv6InvalidCodePoint
    | [] => throw .ipv4InIpv6InvalidCodePoint

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
      let (value, length, afterHex) := readHex 4 0 0 chars
      match afterHex with
      | '.' :: _ =>
        if length = 0 then .error .ipv4InIpv6InvalidCodePoint
        else if st.pieceIndex > 6 then .error .ipv4InIpv6TooManyPieces
        else do
          let (st, seen) ← readIpv4Parts chars.length st 0 chars
          if seen ≠ 4 then throw .ipv4InIpv6TooFewParts
          return st
      | ':' :: afterColon =>
        if afterColon.isEmpty then .error .invalidCodePoint
        else parseLoop fuel (st.setPiece value) afterColon
      | [] => .ok (st.setPiece value)
      | _ => .error .invalidCodePoint

def swapLoop (pieces : Array Nat) (compress : Nat) : Nat → Nat → Array Nat
  | 0, _ => pieces
  | _, 0 => pieces
  | swaps + 1, pieceIndex + 1 =>
    swapLoop (pieces.swapIfInBounds (pieceIndex + 1) (compress + swaps)) compress swaps pieceIndex

def ofPieces (pieces : Array Nat) : Ipv6 :=
  ⟨Vector.ofFn fun i => UInt16.ofNat pieces[i.val]!⟩

def parse (input : String) : Except Ipv6Error Ipv6 := do
  let (st, chars) ←
    match input.toList with
    | ':' :: rest =>
      match rest with
      | ':' :: afterCompression =>
        pure ({ pieceIndex := 1, compress := some 1 : ParseState }, afterCompression)
      | _ => throw .invalidCompression
    | chars => pure ({}, chars)
  let st ← parseLoop (chars.length + 1) st chars
  match st.compress with
  | some compress =>
    return ofPieces (swapLoop st.pieces compress (st.pieceIndex - compress) 7)
  | none =>
    if st.pieceIndex ≠ 8 then throw .tooFewPieces
    return ofPieces st.pieces

def findCompress (pieces : List Nat) : Option Nat :=
  let (_, _, bestStart, bestLength) :=
    pieces.zipIdx.foldl
      (fun (runStart, runLength, bestStart, bestLength) (piece, index) =>
        if piece = 0 then
          let runStart := if runLength = 0 then index else runStart
          let runLength := runLength + 1
          if runLength > bestLength then (runStart, runLength, runStart, runLength)
          else (runStart, runLength, bestStart, bestLength)
        else (0, 0, bestStart, bestLength))
      (0, 0, 0, 0)
  if bestLength > 1 then some bestStart else none

def serialize (address : Ipv6) : String :=
  let pieces := address.pieces.toList.map UInt16.toNat
  let compress := findCompress pieces
  let (output, _) :=
    pieces.zipIdx.foldl
      (fun (output, ignoreZeros) (piece, index) =>
        if ignoreZeros && piece = 0 then (output, ignoreZeros)
        else if compress = some index then
          (output ++ (if index = 0 then "::" else ":"), true)
        else
          (output ++ String.ofList (Nat.toDigits 16 piece) ++ (if index ≠ 7 then ":" else ""), false))
      ("", false)
  output

end Ipv6

end Urllib.Host
