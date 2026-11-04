import UrllibTest.Support
import UrllibTest.Punycode
import Urllib.Punycode.Reference

namespace UrllibTest.PunycodeReference

open Urllib.Punycode

def alphabet : Array Nat :=
  #[0x61, 0x62, 0x2D, 0x30, 0x7A, 0x80, 0xE9, 0xFC, 0x3042, 0x3044, 0x4E2D, 0x05D0, 0x1F600,
    0x10FFFF, 0xD7FF, 0xE000, 0x100]

def nextState (state : Nat) : Nat :=
  (state * 6364136223846793005 + 1442695040888963407) % 18446744073709551616

def generate (seed length : Nat) : String := Id.run do
  let mut state := seed
  let mut chars : List Char := []
  for _ in [0:length] do
    state := nextState state
    chars := Char.ofNat alphabet[(state / 65536) % alphabet.size]! :: chars
  return String.ofList chars

def generatedDisagreements : List Nat :=
  (List.range 3000).filter fun seed =>
    let input := generate (seed * 7919 + 1) (seed % 14)
    encode input != Reference.encode input

/-- info: [] -/
#guard_msgs in
#eval generatedDisagreements

def rfc3492Disagreements : List String :=
  (UrllibTest.Punycode.rfc3492Samples.filter fun sample =>
    encode sample.text != Reference.encode sample.text).map (·.name)

/-- info: [] -/
#guard_msgs in
#eval rfc3492Disagreements

def guardChecks : List UrllibTest.Check := [
  { name := "generates strings of the requested length", holds := (generate 5 9).length == 9 },
  { name := "stops without a pass when no fuel is left", holds := (Reference.encodeLoop 0 [0x100] 0 { n := 128, delta := 0, bias := 72, handled := 0, output := ['x'] }).output == ['x'] }
]

/-- info: [] -/
#guard_msgs in
#eval UrllibTest.failedChecks guardChecks

end UrllibTest.PunycodeReference
