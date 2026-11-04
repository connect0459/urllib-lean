import Urllib.Punycode

namespace Urllib.Punycode

def IsAscii (s : String) : Prop := ∀ c ∈ s.toList, c.toNat < 128

private def AllAscii (cs : List Char) : Prop := ∀ c ∈ cs, c.toNat < 128

private theorem allAscii_nil : AllAscii [] := by
  intro c h
  cases h

private theorem allAscii_cons {c : Char} {cs : List Char} (hc : c.toNat < 128) (h : AllAscii cs) :
    AllAscii (c :: cs) := by
  intro x hx
  cases hx with
  | head => exact hc
  | tail _ hx => exact h x hx

private theorem allAscii_append {a b : List Char} (ha : AllAscii a) (hb : AllAscii b) :
    AllAscii (a ++ b) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · exact hb x h

private theorem digitToChar_lt : ∀ d, d < 36 → (digitToChar d).toNat < 128 := by
  decide

private theorem encodeIntegerFrom_ascii (bias : Nat) : ∀ q k, AllAscii (encodeIntegerFrom bias k q) := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro k
    rw [encodeIntegerFrom]
    have h1 := one_le_threshold k bias
    have h2 := threshold_le k bias
    split
    · exact allAscii_cons (digitToChar_lt q (by omega)) allAscii_nil
    · refine allAscii_cons (digitToChar_lt _ ?_) (ih _ ?_ _)
      · unfold base
        have : (q - threshold k bias) % (36 - threshold k bias) < 36 - threshold k bias :=
          Nat.mod_lt _ (by omega)
        omega
      · unfold base
        exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)

private theorem encodeCodePoint_ascii (basicCount : Nat) (st : EncoderState) (c : Nat)
    (h : AllAscii st.output) : AllAscii (encodeCodePoint basicCount st c).output := by
  unfold encodeCodePoint
  split
  · exact h
  · split
    · exact allAscii_append h (encodeIntegerFrom_ascii _ _ _)
    · exact h

private theorem foldl_encodeCodePoint_ascii (basicCount : Nat) (codePoints : List Nat) :
    ∀ st : EncoderState, AllAscii st.output →
      AllAscii (codePoints.foldl (encodeCodePoint basicCount) st).output := by
  induction codePoints with
  | nil => intro st h; exact h
  | cons c cs ih => intro st h; exact ih _ (encodeCodePoint_ascii basicCount st c h)

private theorem encodeStep_ascii (basicCount : Nat) (codePoints : List Nat) (st : EncoderState)
    (h : AllAscii st.output) : AllAscii (encodeStep basicCount codePoints st).output := by
  unfold encodeStep
  exact foldl_encodeCodePoint_ascii basicCount codePoints _ h

private theorem encodeLoop_ascii (basicCount : Nat) (codePoints : List Nat) :
    ∀ fuel (st : EncoderState), AllAscii st.output →
      AllAscii (encodeLoop basicCount codePoints fuel st).output := by
  intro fuel
  induction fuel with
  | zero => intro st h; exact h
  | succ n ih =>
    intro st h
    unfold encodeLoop
    split
    · exact ih _ (encodeStep_ascii basicCount codePoints st h)
    · exact h

theorem encode_isAscii (input : String) : IsAscii (encode input) := by
  unfold IsAscii encode
  rw [String.toList_ofList]
  apply encodeLoop_ascii
  show AllAscii (if (input.toList.filter (·.toNat < 128)).isEmpty then []
    else (input.toList.filter (·.toNat < 128)) ++ [delimiter])
  split
  · exact allAscii_nil
  · apply allAscii_append
    · intro c hc
      have := (List.mem_filter.mp hc).2
      simpa using this
    · intro c hc
      cases hc with
      | head => decide
      | tail _ h => cases h

end Urllib.Punycode
