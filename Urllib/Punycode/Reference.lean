import Urllib.Punycode

namespace Urllib.Punycode.Reference

open Urllib.Punycode

/-- The state of the scanning encoder of RFC 3492, section 6.3. -/
structure EncoderState where
  /-- The code point value currently being inserted. -/
  n : Nat
  /-- The number of insertions since the last emitted integer. -/
  delta : Nat
  /-- The current bias. -/
  bias : Nat
  /-- The number of code points handled so far. -/
  handled : Nat
  /-- The characters emitted so far. -/
  output : List Char

/-- Processes one input code point: counts it in `delta` when it is below `n`, and emits `delta` when it equals `n`. -/
def encodeCodePoint (basicCount : Nat) (st : EncoderState) (c : Nat) : EncoderState :=
  if c < st.n then
    { st with delta := st.delta + 1 }
  else if c = st.n then
    { st with
      delta := 0
      bias := adapt st.delta (st.handled + 1) (st.handled == basicCount)
      handled := st.handled + 1
      output := st.output ++ encodeIntegerFrom st.bias base st.delta }
  else
    st

/-- One iteration of the outer loop: advances `n` to the smallest unhandled code point and scans the input. -/
def encodeStep (basicCount : Nat) (codePoints : List Nat) (st : EncoderState) : EncoderState :=
  let m := (codePoints.filter (· ≥ st.n)).foldl min 0x110000
  let st := { st with delta := st.delta + (m - st.n) * (st.handled + 1), n := m }
  let st := codePoints.foldl (encodeCodePoint basicCount) st
  { st with delta := st.delta + 1, n := st.n + 1 }

/-- Repeats `encodeStep` until every code point is handled; `fuel` bounds the iterations. -/
def encodeLoop (basicCount : Nat) (codePoints : List Nat) : Nat → EncoderState → EncoderState
  | 0, st => st
  | fuel + 1, st =>
    if st.handled < codePoints.length then
      encodeLoop basicCount codePoints fuel (encodeStep basicCount codePoints st)
    else
      st

/-- The scanning encoder of RFC 3492, kept as a reference and proved equal to `Punycode.encode`. -/
def encode (input : String) : String :=
  let codePoints := input.toList.map Char.toNat
  let basic := input.toList.filter (·.toNat < 128)
  let basicPrefix := if basic.isEmpty then [] else basic ++ [delimiter]
  let initial : EncoderState :=
    { n := initialN, delta := 0, bias := initialBias, handled := basic.length, output := basicPrefix }
  String.ofList (encodeLoop basic.length codePoints (codePoints.length + 1) initial).output

end Urllib.Punycode.Reference
