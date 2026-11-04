import Urllib.Host.Ipv4

namespace Urllib.Host.Ipv4

private theorem digits_parse : ∀ b, b < 256 → parseNumber? (Nat.toDigits 10 b) = some b := by
  decide +kernel

private theorem digits_no_dot : ∀ b, b < 256 → ∀ c ∈ Nat.toDigits 10 b, c ≠ '.' := by
  decide +kernel

private theorem digits_ne_nil : ∀ b, b < 256 → Nat.toDigits 10 b ≠ [] := by
  decide +kernel

private theorem splitDots_cons (c : Char) (l : List Char) :
    splitDots (c :: l) =
      (match splitDots l with
       | part :: more => if c = '.' then [] :: part :: more else (c :: part) :: more
       | [] => [[]]) := rfl

private theorem splitDots_ne_nil : ∀ l, splitDots l ≠ [] := by
  intro l
  induction l with
  | nil => simp [splitDots]
  | cons c rest ih =>
    rw [splitDots_cons]
    split
    · rename_i part more heq
      by_cases hc : c = '.' <;> simp [hc]
    · rename_i heq
      exact absurd heq ih

private theorem splitDots_no_dot : ∀ ds : List Char, (∀ c ∈ ds, c ≠ '.') → splitDots ds = [ds] := by
  intro ds
  induction ds with
  | nil => intro _; rfl
  | cons c ds ih =>
    intro h
    have hc : c ≠ '.' := h c (by simp)
    have hds : ∀ x ∈ ds, x ≠ '.' := fun x hx => h x (by simp [hx])
    unfold splitDots
    rw [ih hds]
    simp [hc]

private theorem splitDots_append : ∀ (ds rest : List Char), (∀ c ∈ ds, c ≠ '.') →
    splitDots (ds ++ '.' :: rest) = ds :: splitDots rest := by
  intro ds rest
  induction ds with
  | nil =>
    intro _
    obtain ⟨part, more, h⟩ := List.exists_cons_of_ne_nil (splitDots_ne_nil rest)
    simp [splitDots, h]
  | cons c ds ih =>
    intro h
    have hc : c ≠ '.' := h c (by simp)
    have hds : ∀ x ∈ ds, x ≠ '.' := fun x hx => h x (by simp [hx])
    simp only [List.cons_append]
    rw [splitDots_cons, ih hds]
    simp [hc]

private theorem parseChars_digits (b1 b2 b3 b4 : Nat)
    (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256) (h4 : b4 < 256) :
    parseChars (Nat.toDigits 10 b1 ++ '.' :: (Nat.toDigits 10 b2 ++ '.' ::
        (Nat.toDigits 10 b3 ++ '.' :: Nat.toDigits 10 b4))) =
      .ok ⟨UInt32.ofNat (b4 + b1 * 256 ^ 3 + b2 * 256 ^ 2 + b3 * 256)⟩ := by
  have hparts : splitDots (Nat.toDigits 10 b1 ++ '.' :: (Nat.toDigits 10 b2 ++ '.' ::
        (Nat.toDigits 10 b3 ++ '.' :: Nat.toDigits 10 b4))) =
      [Nat.toDigits 10 b1, Nat.toDigits 10 b2, Nat.toDigits 10 b3, Nat.toDigits 10 b4] := by
    rw [splitDots_append _ _ (digits_no_dot b1 h1), splitDots_append _ _ (digits_no_dot b2 h2),
      splitDots_append _ _ (digits_no_dot b3 h3), splitDots_no_dot _ (digits_no_dot b4 h4)]
  obtain ⟨c, cs, hd4⟩ := List.exists_cons_of_ne_nil (digits_ne_nil b4 h4)
  have hsp : splitParts (Nat.toDigits 10 b1 ++ '.' :: (Nat.toDigits 10 b2 ++ '.' ::
        (Nat.toDigits 10 b3 ++ '.' :: Nat.toDigits 10 b4))) =
      [Nat.toDigits 10 b1, Nat.toDigits 10 b2, Nat.toDigits 10 b3, Nat.toDigits 10 b4] := by
    unfold splitParts
    rw [hparts, hd4]
    simp
  unfold parseChars
  rw [hsp]
  simp [List.mapM_cons, digits_parse b1 h1, digits_parse b2 h2, digits_parse b3 h3,
    digits_parse b4 h4]
  have hc1 : ¬ (255 < b1 ∨ 255 < b2 ∨ 255 < b3) := by omega
  have hc2 : ¬ 256 ≤ b4 := by omega
  simp [hc1, hc2]
  rfl

theorem parse_serialize (a : Ipv4) : parse a.serialize = .ok a := by
  have hn : a.value.toNat < 4294967296 := a.value.toNat_lt_size
  unfold parse serialize
  rw [String.toList_ofList]
  show parseChars (Nat.toDigits 10 (a.value.toNat / 2 ^ 24 % 256) ++ '.' ::
      (Nat.toDigits 10 (a.value.toNat / 2 ^ 16 % 256) ++ '.' ::
        (Nat.toDigits 10 (a.value.toNat / 2 ^ 8 % 256) ++ '.' ::
          Nat.toDigits 10 (a.value.toNat / 2 ^ 0 % 256)))) = _
  rw [parseChars_digits _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
  have hsum : a.value.toNat / 2 ^ 0 % 256 + a.value.toNat / 2 ^ 24 % 256 * 256 ^ 3 +
      a.value.toNat / 2 ^ 16 % 256 * 256 ^ 2 + a.value.toNat / 2 ^ 8 % 256 * 256 = a.value.toNat := by
    omega
  rw [hsum, UInt32.ofNat_toNat]

end Urllib.Host.Ipv4
