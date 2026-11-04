import Urllib.Punycode

namespace Urllib.Punycode.Reference

open Urllib.Punycode

structure EncoderState where
  n : Nat
  delta : Nat
  bias : Nat
  handled : Nat
  output : List Char

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

def encodeStep (basicCount : Nat) (codePoints : List Nat) (st : EncoderState) : EncoderState :=
  let m := (codePoints.filter (· ≥ st.n)).foldl min 0x110000
  let st := { st with delta := st.delta + (m - st.n) * (st.handled + 1), n := m }
  let st := codePoints.foldl (encodeCodePoint basicCount) st
  { st with delta := st.delta + 1, n := st.n + 1 }

def encodeLoop (basicCount : Nat) (codePoints : List Nat) : Nat → EncoderState → EncoderState
  | 0, st => st
  | fuel + 1, st =>
    if st.handled < codePoints.length then
      encodeLoop basicCount codePoints fuel (encodeStep basicCount codePoints st)
    else
      st

def encode (input : String) : String :=
  let codePoints := input.toList.map Char.toNat
  let basic := input.toList.filter (·.toNat < 128)
  let basicPrefix := if basic.isEmpty then [] else basic ++ [delimiter]
  let initial : EncoderState :=
    { n := initialN, delta := 0, bias := initialBias, handled := basic.length, output := basicPrefix }
  String.ofList (encodeLoop basic.length codePoints (codePoints.length + 1) initial).output

end Urllib.Punycode.Reference
