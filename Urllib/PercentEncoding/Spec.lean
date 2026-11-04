import Urllib.PercentEncoding

namespace Urllib.PercentEncoding

theorem decodeBytes_percentEncodeByte :
    ∀ n, n < 256 →
      decodeBytes (percentEncodeByte (UInt8.ofNat n)).toUTF8.data.toList = [UInt8.ofNat n] := by
  decide +kernel

theorem component_contains_percent : EncodeSet.component.contains '%' = true := by
  decide

theorem userinfo_lacks_percent : EncodeSet.userinfo.contains '%' = false := by
  decide

private theorem utf8_data_toList (cs : List Char) :
    (String.ofList cs).toUTF8.data.toList = cs.flatMap String.utf8EncodeChar := by
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
  simp [List.utf8Encode]

private theorem singleton_bytes (c : Char) :
    (String.singleton c).toUTF8.data.toList = String.utf8EncodeChar c := by
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_singleton, List.utf8Encode_singleton]
  simp

private theorem hexValue_escape : ∀ n, n < 256 →
    (percentEncodeByteChars (UInt8.ofNat n)).flatMap String.utf8EncodeChar =
        [0x25, (hexDigit (n / 16)).toNat.toUInt8, (hexDigit (n % 16)).toNat.toUInt8] ∧
      hexValue? ((hexDigit (n / 16)).toNat.toUInt8) = some (n / 16) ∧
      hexValue? ((hexDigit (n % 16)).toNat.toUInt8) = some (n % 16) := by
  decide +kernel

private theorem decodeBytes_nonPercent (b : UInt8) (l : List UInt8) (h : b ≠ 0x25) :
    decodeBytes (b :: l) = b :: decodeBytes l := by
  rw [decodeBytes]
  · intro h1 h2 rest hh
    exact fun _ => h hh

private theorem decodeBytes_escape (n : Nat) (hn : n < 256) (rest : List UInt8) :
    decodeBytes ([0x25, (hexDigit (n / 16)).toNat.toUInt8, (hexDigit (n % 16)).toNat.toUInt8] ++ rest) =
      UInt8.ofNat n :: decodeBytes rest := by
  obtain ⟨_, hv1, hv2⟩ := hexValue_escape n hn
  rw [List.cons_append, List.cons_append, List.cons_append, List.nil_append, decodeBytes]
  simp only [hv1, hv2]
  congr 2
  omega

private theorem decodeBytes_append_noPercent : ∀ (xs rest : List UInt8), (∀ b ∈ xs, b ≠ 0x25) →
    decodeBytes (xs ++ rest) = xs ++ decodeBytes rest := by
  intro xs
  induction xs with
  | nil => intro rest _; simp
  | cons b xs ih =>
    intro rest h
    rw [List.cons_append, decodeBytes_nonPercent b _ (h b (by simp)), ih rest (fun x hx => h x (by simp [hx]))]
    simp

private theorem decodeBytes_append_escapes : ∀ (bytes : List UInt8) (rest : List UInt8),
    decodeBytes (((bytes.flatMap percentEncodeByteChars).flatMap String.utf8EncodeChar) ++ rest) =
      bytes ++ decodeBytes rest := by
  intro bytes
  induction bytes with
  | nil => intro rest; simp
  | cons b bs ih =>
    intro rest
    obtain ⟨he, _⟩ := hexValue_escape b.toNat b.toNat_lt
    have hb : UInt8.ofNat b.toNat = b := UInt8.ofNat_toNat
    rw [hb] at he
    rw [List.flatMap_cons, List.flatMap_append, he, List.append_assoc]
    have := decodeBytes_escape b.toNat b.toNat_lt (((bs.flatMap percentEncodeByteChars).flatMap
      String.utf8EncodeChar) ++ rest)
    rw [this, hb, ih]
    simp

private theorem ofNat_ne_percent (x : Nat) (h : x % 256 ≠ 37) : UInt8.ofNat x ≠ 0x25 := by
  intro e
  have := congrArg UInt8.toNat e
  simp at this
  omega

private theorem char_percent_of_toNat (c : Char) (h : c.val.toNat = 37) : c = '%' := by
  have h' : c.toNat = 37 := h
  calc c = Char.ofNat c.toNat := (Char.ofNat_toNat c).symm
    _ = Char.ofNat 37 := by rw [h']
    _ = '%' := by decide

private theorem utf8EncodeChar_ne_percent (c : Char) (hc : c ≠ '%') :
    ∀ b ∈ String.utf8EncodeChar c, b ≠ 0x25 := by
  intro b hb
  unfold String.utf8EncodeChar at hb
  dsimp only at hb
  split at hb
  · rename_i h1
    simp only [List.mem_singleton] at hb
    subst hb
    apply ofNat_ne_percent
    intro e
    have : c.val.toNat = 37 := by omega
    exact hc (char_percent_of_toNat c this)
  · split at hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> apply ofNat_ne_percent <;> omega
    · split at hb
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl <;> apply ofNat_ne_percent <;> omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> apply ofNat_ne_percent <;> omega

private theorem decode_codePoint (set : EncodeSet) (c : Char) (rest : List UInt8)
    (h : set.contains c = true ∨ c ≠ '%') :
    decodeBytes (((utf8PercentEncodeCodePointChars set c).flatMap String.utf8EncodeChar) ++ rest) =
      String.utf8EncodeChar c ++ decodeBytes rest := by
  unfold utf8PercentEncodeCodePointChars
  by_cases hc : set.contains c = true
  · simp only [hc, ite_true]
    rw [singleton_bytes]
    exact decodeBytes_append_escapes _ rest
  · have hne : c ≠ '%' := by
      rcases h with h | h
      · exact absurd h hc
      · exact h
    have hc' : set.contains c = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ite_false, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact decodeBytes_append_noPercent _ rest (utf8EncodeChar_ne_percent c hne)

private theorem decode_chars (set : EncodeSet) : ∀ cs : List Char,
    (∀ c ∈ cs, set.contains c = true ∨ c ≠ '%') →
    decodeBytes ((cs.flatMap (utf8PercentEncodeCodePointChars set)).flatMap String.utf8EncodeChar) =
      cs.flatMap String.utf8EncodeChar := by
  intro cs
  induction cs with
  | nil => intro _; simp [decodeBytes]
  | cons c cs ih =>
    intro h
    rw [List.flatMap_cons, List.flatMap_append,
      decode_codePoint set c _ (h c (by simp)), ih (fun x hx => h x (by simp [hx]))]
    simp

theorem percentDecode_utf8PercentEncode (set : EncodeSet) (s : String)
    (h : set.contains '%' = true ∨ '%' ∉ s.toList) :
    percentDecode (utf8PercentEncode set s).toUTF8 = s.toUTF8 := by
  have hall : ∀ c ∈ s.toList, set.contains c = true ∨ c ≠ '%' := by
    intro c hc
    rcases h with h | h
    · by_cases hcp : c = '%'
      · left; rw [hcp]; exact h
      · right; exact hcp
    · right; intro e; exact h (e ▸ hc)
  unfold percentDecode utf8PercentEncode
  rw [utf8_data_toList, decode_chars set s.toList hall]
  have hs : s.toUTF8.data.toList = s.toList.flatMap String.utf8EncodeChar := by
    rw [← utf8_data_toList, String.ofList_toList]
  have hdata : s.toUTF8.data = (s.toList.flatMap String.utf8EncodeChar).toArray := by
    apply Array.toList_inj.mp
    simpa using hs
  cases hb : s.toUTF8 with
  | mk d =>
    rw [hb] at hdata
    simp only at hdata
    rw [hdata]

theorem percentDecode_utf8PercentEncode_component (s : String) :
    percentDecode (utf8PercentEncode .component s).toUTF8 = s.toUTF8 :=
  percentDecode_utf8PercentEncode .component s (Or.inl component_contains_percent)

private theorem utf8EncodeChar_ascii (c : Char) (h : c.toNat < 128) :
    String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
  have h0 : c.val.toNat ≤ 0x7f := by
    have : c.toNat = c.val.toNat := rfl
    omega
  unfold String.utf8EncodeChar
  dsimp only
  simp only [h0, ↓reduceIte]
  rfl

private theorem decodeUtf8Loop_ascii : ∀ (cs : List Char) (acc : List Char),
    (∀ c ∈ cs, c.toNat < 128) →
    decodeUtf8Loop {} (cs.flatMap String.utf8EncodeChar) acc = cs.reverse ++ acc := by
  intro cs
  induction cs with
  | nil => intro acc _; simp [decodeUtf8Loop]
  | cons c cs ih =>
    intro acc h
    have hc : c.toNat < 128 := h c (by simp)
    rw [List.flatMap_cons, utf8EncodeChar_ascii c hc, List.singleton_append, decodeUtf8Loop]
    have hn : (UInt8.ofNat c.toNat).toNat = c.toNat := by simp; omega
    have hfeed : feed {} (UInt8.ofNat c.toNat).toNat acc = ({}, c :: acc) := by
      rw [hn]
      unfold feed feedLead
      have : c.toNat ≤ 0x7F := by omega
      simp [this, Char.ofNat_toNat]
    simp only [hfeed]
    rw [ih (c :: acc) (fun x hx => h x (by simp [hx]))]
    simp

theorem utf8DecodeWithoutBom_percentDecodeString_ascii (s : String)
    (h : ∀ c ∈ s.toList, c.toNat < 128 ∧ c ≠ '%') :
    utf8DecodeWithoutBom (percentDecodeString s) = s := by
  have hbytes : s.toUTF8.data.toList = s.toList.flatMap String.utf8EncodeChar := by
    rw [← utf8_data_toList, String.ofList_toList]
  have hnopct : ∀ b ∈ s.toList.flatMap String.utf8EncodeChar, b ≠ 0x25 := by
    intro b hb
    obtain ⟨c, hc, hbc⟩ := List.mem_flatMap.mp hb
    exact utf8EncodeChar_ne_percent c (h c hc).2 b hbc
  have hdec : (percentDecodeString s).data.toList = s.toList.flatMap String.utf8EncodeChar := by
    unfold percentDecodeString percentDecode
    simp only [hbytes]
    have := decodeBytes_append_noPercent (s.toList.flatMap String.utf8EncodeChar) [] hnopct
    simpa [decodeBytes] using this
  have hascii : ∀ c ∈ s.toList, c.toNat < 128 := fun c hc => (h c hc).1
  unfold utf8DecodeWithoutBom
  rw [hdec]
  dsimp only
  have hnobom : ∀ rest, s.toList.flatMap String.utf8EncodeChar ≠ 0xEF :: 0xBB :: 0xBF :: rest := by
    intro rest hr
    cases hs : s.toList with
    | nil => simp [hs] at hr
    | cons c cs =>
      rw [hs, List.flatMap_cons, utf8EncodeChar_ascii c (hascii c (by simp [hs]))] at hr
      have := (List.cons.inj hr).1
      have h2 := congrArg UInt8.toNat this
      have h3 := hascii c (by simp [hs])
      simp at h2
      omega
  split
  · rename_i rest heq
    exact absurd heq (hnobom rest)
  · rw [decodeUtf8Loop_ascii s.toList [] hascii]
    simp

/-- The output shape of `utf8PercentEncode`: characters outside the set kept as is, and escapes of single bytes. -/
inductive WellEncoded (set : EncodeSet) : List Char → Prop where
  /-- The empty sequence is well encoded. -/
  | nil : WellEncoded set []
  /-- A character outside the set may be kept as is. -/
  | raw (c : Char) (rest : List Char) :
      set.contains c = false → WellEncoded set rest → WellEncoded set (c :: rest)
  /-- The escape of a single byte is well encoded. -/
  | escape (b : UInt8) (rest : List Char) :
      WellEncoded set rest → WellEncoded set (percentEncodeByteChars b ++ rest)

theorem WellEncoded.append {set : EncodeSet} {l₁ l₂ : List Char}
    (h₁ : WellEncoded set l₁) (h₂ : WellEncoded set l₂) : WellEncoded set (l₁ ++ l₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | raw c rest hc _ ih => exact WellEncoded.raw c _ hc ih
  | escape b rest _ ih =>
    rw [List.append_assoc]
    exact WellEncoded.escape b _ ih

private theorem wellEncoded_escapes (set : EncodeSet) : ∀ bytes : List UInt8,
    WellEncoded set (bytes.flatMap percentEncodeByteChars) := by
  intro bytes
  induction bytes with
  | nil => exact WellEncoded.nil
  | cons b bs ih =>
    rw [List.flatMap_cons]
    exact WellEncoded.escape b _ ih

private theorem wellEncoded_codePoint (set : EncodeSet) (c : Char) :
    WellEncoded set (utf8PercentEncodeCodePointChars set c) := by
  unfold utf8PercentEncodeCodePointChars
  by_cases hc : set.contains c = true
  · simp only [hc, ite_true]
    exact wellEncoded_escapes set _
  · have hc' : set.contains c = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ite_false]
    exact WellEncoded.raw c [] hc' WellEncoded.nil

private theorem wellEncoded_flatMap (set : EncodeSet) : ∀ cs : List Char,
    WellEncoded set (cs.flatMap (utf8PercentEncodeCodePointChars set)) := by
  intro cs
  induction cs with
  | nil => exact WellEncoded.nil
  | cons c cs ih =>
    rw [List.flatMap_cons]
    exact (wellEncoded_codePoint set c).append ih

theorem utf8PercentEncode_wellEncoded (set : EncodeSet) (input : String) :
    WellEncoded set (utf8PercentEncode set input).toList := by
  unfold utf8PercentEncode
  rw [String.toList_ofList]
  exact wellEncoded_flatMap set _

theorem percentEncodeByteChars_form (b : UInt8) :
    ∃ hi lo, hi < 16 ∧ lo < 16 ∧ percentEncodeByteChars b = ['%', hexDigit hi, hexDigit lo] := by
  have := b.toNat_lt
  exact ⟨b.toNat / 16, b.toNat % 16, by omega, Nat.mod_lt _ (by omega), rfl⟩

theorem hexDigit_upper_hex : ∀ n, n < 16 →
    ('0' ≤ hexDigit n ∧ hexDigit n ≤ '9') ∨ ('A' ≤ hexDigit n ∧ hexDigit n ≤ 'F') := by
  decide

end Urllib.PercentEncoding
