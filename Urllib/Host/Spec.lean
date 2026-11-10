import Urllib.Host
import Urllib.Host.Ipv4.Spec
import Urllib.Host.Ipv6.Spec
import Urllib.Idna.Spec
import Urllib.PercentEncoding.Spec
namespace Urllib.Host

open Urllib
private theorem ascii_char_cases (P : Char → Prop) (hP : ∀ n, n < 128 → P (Char.ofNat n)) (c : Char)
    (h : c.toNat < 128) : P c := by
  have : c = Char.ofNat c.toNat := (Char.ofNat_toNat c).symm
  rw [this]
  exact hP c.toNat h

private theorem toLower_ascii (c : Char) (h : c.toNat < 128) :
    c.toLower.toNat < 128 ∧ c.toLower.toLower = c.toLower := by
  refine ascii_char_cases (fun c => c.toLower.toNat < 128 ∧ c.toLower.toLower = c.toLower) ?_ c h
  decide

private theorem isDigit_ascii (c : Char) (h : c.isDigit = true) : c.toNat < 128 := by
  unfold Char.isDigit at h
  simp at h
  have := h.2
  have h2 : c.val.toNat ≤ 57 := by simpa [UInt32.le_iff_toNat_le] using this
  have : c.toNat = c.val.toNat := rfl
  omega

private theorem digit_dot_props (c : Char) (h : c.isDigit = true ∨ c = '.') :
    c.toNat < 128 ∧ c ≠ '%' ∧ c.toLower = c ∧ Host.isForbiddenDomainCodePoint c = false := by
  have hlt : c.toNat < 128 := by
    rcases h with h | rfl
    · exact isDigit_ascii c h
    · decide
  refine ascii_char_cases (fun c => (c.isDigit = true ∨ c = '.') →
    (c.toNat < 128 ∧ c ≠ '%' ∧ c.toLower = c ∧ Host.isForbiddenDomainCodePoint c = false)) ?_ c hlt h
  decide

private theorem domainToAscii_stable (asc : List Char) (hascii : ∀ c ∈ asc, c.toNat < 128)
    (hlow : asc.map Char.toLower = asc) (hne : asc ≠ []) :
    Host.domainToAscii asc = .ok asc := by
  unfold Host.domainToAscii
  have h1 : (asc.any fun (c : Char) => decide (128 ≤ c.toNat)) = false := by
    simp only [List.any_eq_false, decide_eq_true_eq]
    intro c hc
    have := hascii c hc
    omega
  have h2 : asc.isEmpty = false := by
    cases asc with
    | nil => exact absurd rfl hne
    | cons c cs => rfl
  simp [h1, hlow, h2]

private theorem parseDomain_stable (asc : List Char) (hascii : ∀ c ∈ asc, c.toNat < 128 ∧ c ≠ '%')
    (hlow : asc.map Char.toLower = asc) (hne : asc ≠ [])
    (hforb : asc.any Host.isForbiddenDomainCodePoint = false) :
    Host.parseDomain asc =
      (if Ipv4.endsInNumber (String.ofList asc) = true then
        (match Ipv4.parse (String.ofList asc) with
         | .ok a => .ok (.ipv4 a)
         | .error e => .error (.ipv4 e))
       else .ok (.domain (String.ofList asc))) := by
  have hdec : PercentEncoding.utf8DecodeWithoutBom
      (PercentEncoding.percentDecodeString (String.ofList asc)) = String.ofList asc :=
    PercentEncoding.utf8DecodeWithoutBom_percentDecodeString_ascii _
      (by rw [String.toList_ofList]; exact hascii)
  have hd := domainToAscii_stable asc (fun c hc => (hascii c hc).1) hlow hne
  unfold Host.parseDomain
  simp only [hdec, String.toList_ofList, hd, hforb, Bool.false_eq_true, ite_false, bind,
    Except.bind, pure, Except.pure]
  by_cases he : Ipv4.endsInNumber (String.ofList asc) = true
  · simp only [he, ite_true]
    cases Ipv4.parse (String.ofList asc) <;> rfl
  · have he' : Ipv4.endsInNumber (String.ofList asc) = false := by simpa using he
    simp [he']

private theorem parseChars_nonBracket (input : List Char) (isOpaque : Bool)
    (h : ∀ rest, input ≠ '[' :: rest) :
    Host.parseChars input isOpaque =
      if isOpaque then Host.parseOpaque input else Host.parseDomain input := by
  cases input with
  | nil => rfl
  | cons c rest =>
    by_cases hc : c = '['
    · exact absurd (by rw [hc]) (h rest)
    · unfold Host.parseChars
      split
      · rename_i r heq
        exact absurd heq (h r)
      · rfl

theorem parse_serialize_ipv6 (a : Host.Ipv6) (isOpaque : Bool) :
    Host.parse (Host.serialize (.ipv6 a)) isOpaque = .ok (.ipv6 a) := by
  have hl : (Host.serialize (.ipv6 a)).toList = '[' :: (a.serialize.toList ++ [']']) := by
    simp [Host.serialize, String.toList_append]
  unfold Host.parse
  rw [hl]
  unfold Host.parseChars
  have hlast : (a.serialize.toList ++ [']']).getLast? = some ']' := by simp
  have hdrop : (a.serialize.toList ++ [']']).dropLast = a.serialize.toList := by simp
  simp only [hlast, ite_true, hdrop, String.ofList_toList]
  rw [Host.Ipv6.parse_serialize]

theorem parse_serialize_ipv4 (a : Host.Ipv4) :
    Host.parse (Host.serialize (.ipv4 a)) false = .ok (.ipv4 a) := by
  have hl : (Host.serialize (.ipv4 a)).toList = Host.Ipv4.serializeChars a := by
    simp [Host.serialize, Host.Ipv4.serialize]
  have hprops := fun c (hc : c ∈ Host.Ipv4.serializeChars a) =>
    digit_dot_props c (Host.Ipv4.serializeChars_digit_or_dot a c hc)
  have hnb : ∀ rest, Host.Ipv4.serializeChars a ≠ '[' :: rest := by
    intro rest h
    have := Host.Ipv4.serializeChars_digit_or_dot a '[' (by rw [h]; simp)
    revert this
    decide
  unfold Host.parse
  rw [hl, parseChars_nonBracket _ _ hnb]
  simp only [Bool.false_eq_true, ite_false]
  rw [parseDomain_stable (Host.Ipv4.serializeChars a)
    (fun c hc => ⟨(hprops c hc).1, (hprops c hc).2.1⟩)
    (by
      rw [List.map_congr_left (fun c hc => (hprops c hc).2.2.1)]
      simp)
    (by simp [Host.Ipv4.serializeChars])
    (by
      simp only [List.any_eq_false]
      intro c hc
      simpa using (hprops c hc).2.2.2)]
  have hs : String.ofList (Host.Ipv4.serializeChars a) = Host.Ipv4.serialize a := rfl
  rw [hs]
  simp only [Host.Ipv4.endsInNumber_serialize, ite_true]
  rw [Host.Ipv4.parse_serialize]

private theorem pct_props : ∀ n, n < 256 → ∀ d ∈ PercentEncoding.percentEncodeByteChars (UInt8.ofNat n),
    PercentEncoding.EncodeSet.c0Control.contains d = false ∧
      Host.isForbiddenHostCodePoint d = false := by
  decide +kernel

private theorem enc_props (input : List Char) (hf : ∀ c ∈ input, Host.isForbiddenHostCodePoint c = false) :
    ∀ c ∈ input, ∀ d ∈ PercentEncoding.utf8PercentEncodeCodePointChars .c0Control c,
      PercentEncoding.EncodeSet.c0Control.contains d = false ∧
        Host.isForbiddenHostCodePoint d = false := by
  intro c hc d hd
  unfold PercentEncoding.utf8PercentEncodeCodePointChars at hd
  by_cases hs : PercentEncoding.EncodeSet.c0Control.contains c = true
  · simp only [hs, ite_true] at hd
    obtain ⟨b, _, hdb⟩ := List.mem_flatMap.mp hd
    have := pct_props b.toNat b.toNat_lt
    rw [UInt8.ofNat_toNat] at this
    exact this d hdb
  · have hs' : PercentEncoding.EncodeSet.c0Control.contains c = false := by simpa using hs
    simp only [hs', Bool.false_eq_true, ite_false, List.mem_singleton] at hd
    subst hd
    exact ⟨hs', hf _ hc⟩

private theorem flatMap_enc_id (L : List Char)
    (h : ∀ d ∈ L, PercentEncoding.EncodeSet.c0Control.contains d = false) :
    L.flatMap (PercentEncoding.utf8PercentEncodeCodePointChars .c0Control) = L := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    have hd := h d (by simp)
    have : PercentEncoding.utf8PercentEncodeCodePointChars .c0Control d = [d] := by
      unfold PercentEncoding.utf8PercentEncodeCodePointChars
      simp [hd]
    rw [List.flatMap_cons, this, ih (fun x hx => h x (by simp [hx]))]
    rfl

private theorem enc_ne_nil (c : Char) :
    PercentEncoding.utf8PercentEncodeCodePointChars .c0Control c ≠ [] := by
  unfold PercentEncoding.utf8PercentEncodeCodePointChars
  split
  · have hl : (String.singleton c).toUTF8.data.toList ≠ [] := by
      have h : (String.singleton c).toUTF8.data.toList = String.utf8EncodeChar c := by
        rw [String.toUTF8_eq_toByteArray, String.toByteArray_singleton, List.utf8Encode_singleton]
        simp
      rw [h]
      exact String.utf8EncodeChar_ne_nil
    obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil hl
    rw [hb]
    simp [PercentEncoding.percentEncodeByteChars]
  · simp

private theorem parseOpaque_of_ne_nil (input : List Char) (hne : input ≠ []) :
    Host.parseOpaque input =
      if input.any Host.isForbiddenHostCodePoint then .error .forbiddenHostCodePoint
      else .ok (.opaqueHost (PercentEncoding.utf8PercentEncode .c0Control (String.ofList input))) := by
  cases input with
  | nil => exact absurd rfl hne
  | cons c cs => rfl

private theorem parse_serialize_opaque (input : List Char) (t : String) (hne : input ≠ [])
    (hp : Host.parseOpaque input = .ok (.opaqueHost t)) :
    Host.parseChars t.toList true = .ok (.opaqueHost t) := by
  rw [parseOpaque_of_ne_nil input hne] at hp
  by_cases hany : input.any Host.isForbiddenHostCodePoint = true
  · simp [hany] at hp
  · have hany' : input.any Host.isForbiddenHostCodePoint = false := by simpa using hany
    simp only [hany', Bool.false_eq_true, ite_false, Except.ok.injEq, Host.opaqueHost.injEq] at hp
    have hf : ∀ c ∈ input, Host.isForbiddenHostCodePoint c = false := by
      simpa [List.any_eq_false] using hany'
    have ht : t.toList = input.flatMap (PercentEncoding.utf8PercentEncodeCodePointChars .c0Control) := by
      rw [← hp]
      simp [PercentEncoding.utf8PercentEncode]
    have hprops := enc_props input hf
    have hL : ∀ d ∈ t.toList, PercentEncoding.EncodeSet.c0Control.contains d = false ∧
        Host.isForbiddenHostCodePoint d = false := by
      intro d hd
      rw [ht] at hd
      obtain ⟨c, hc, hdc⟩ := List.mem_flatMap.mp hd
      exact hprops c hc d hdc
    have htne : t.toList ≠ [] := by
      rw [ht]
      obtain ⟨c0, cs0, rfl⟩ := List.exists_cons_of_ne_nil hne
      simp only [List.flatMap_cons, ne_eq, List.append_eq_nil_iff, not_and]
      exact fun h => absurd h (enc_ne_nil c0)
    have hnb : ∀ rest, t.toList ≠ '[' :: rest := by
      intro rest h
      have := (hL '[' (by rw [h]; simp)).2
      revert this
      decide
    rw [parseChars_nonBracket _ _ hnb]
    simp only [ite_true]
    obtain ⟨d0, ds0, hd0⟩ := List.exists_cons_of_ne_nil htne
    unfold Host.parseOpaque
    rw [hd0]
    dsimp only
    rw [← hd0]
    have hany2 : t.toList.any Host.isForbiddenHostCodePoint = false := by
      simp only [List.any_eq_false]
      intro d hd
      simpa using (hL d hd).2
    simp only [hany2, Bool.false_eq_true, ite_false]
    have hid : t.toList.flatMap (PercentEncoding.utf8PercentEncodeCodePointChars .c0Control) = t.toList :=
      flatMap_enc_id _ (fun d hd => (hL d hd).1)
    congr 2
    simp [PercentEncoding.utf8PercentEncode, hid]

private theorem domainToAscii_ok_props (d asc : List Char) (h : Host.domainToAscii d = .ok asc) :
    (∀ c ∈ asc, c.toNat < 128) ∧ asc.map Char.toLower = asc ∧ asc ≠ [] := by
  unfold Host.domainToAscii at h
  by_cases h1 : (d.any fun (c : Char) => decide (128 ≤ c.toNat)) = true
  · simp only [h1, ite_true] at h
    cases hr : Idna.toAsciiChars (Idna.Options.whatwg false) d with
    | error e => simp [hr] at h
    | ok r =>
      simp only [hr] at h
      by_cases hemp : r.isEmpty = true
      · simp [hemp] at h
      · have hemp' : r.isEmpty = false := by simpa using hemp
        simp only [hemp', Bool.false_eq_true, ite_false, Except.ok.injEq] at h
        subst h
        have hclean := Idna.toAsciiChars_ok_clean _ rfl rfl d r hr
        refine ⟨fun c hc => (hclean c hc).1, ?_, ?_⟩
        · calc r.map Char.toLower = r.map id :=
                List.map_congr_left (fun c hc => Idna.clean_toLower c (hclean c hc))
            _ = r := List.map_id _
        · intro e
          simp [e] at hemp'
  · have h1' : (d.any fun (c : Char) => decide (128 ≤ c.toNat)) = false := by simpa using h1
    simp only [h1', Bool.false_eq_true, ite_false] at h
    by_cases h2 : (d.map Char.toLower).isEmpty = true
    · simp [h2] at h
    · have h2' : (d.map Char.toLower).isEmpty = false := by simpa using h2
      simp only [h2', Bool.false_eq_true, ite_false, Except.ok.injEq] at h
      simp only [List.any_eq_false, decide_eq_true_eq] at h1'
      have hd : ∀ c ∈ d, c.toNat < 128 := fun c hc => by have := h1' c hc; omega
      refine ⟨?_, ?_, ?_⟩
      · intro c hc
        rw [← h] at hc
        obtain ⟨e, he2, rfl⟩ := List.mem_map.mp hc
        exact (toLower_ascii e (hd e he2)).1
      · rw [← h, List.map_map]
        apply List.map_congr_left
        intro e he2
        exact (toLower_ascii e (hd e he2)).2
      · rw [← h]
        intro e
        rw [e] at h2'
        simp at h2'

private theorem parseDomain_cases (input : List Char) (h : Host) (hp : Host.parseDomain input = .ok h) :
    (∃ a, h = .ipv4 a) ∨
      (∃ asc, h = .domain (String.ofList asc) ∧ (∀ c ∈ asc, c.toNat < 128 ∧ c ≠ '%') ∧
        asc.map Char.toLower = asc ∧ asc ≠ [] ∧ asc.any Host.isForbiddenDomainCodePoint = false ∧
        Ipv4.endsInNumber (String.ofList asc) = false) := by
  unfold Host.parseDomain at hp
  generalize PercentEncoding.utf8DecodeWithoutBom
    (PercentEncoding.percentDecodeString (String.ofList input)) = dom at hp
  cases hd : Host.domainToAscii dom.toList with
  | error e => simp [hd, bind, Except.bind] at hp
  | ok asc =>
    simp only [hd, bind, Except.bind] at hp
    by_cases hf : asc.any Host.isForbiddenDomainCodePoint = true
    · simp [hf] at hp
    · have hf' : asc.any Host.isForbiddenDomainCodePoint = false := by simpa using hf
      simp only [hf', Bool.false_eq_true, ite_false] at hp
      by_cases he : Ipv4.endsInNumber (String.ofList asc) = true
      · left
        simp only [he, ite_true] at hp
        cases hpa : Ipv4.parse (String.ofList asc) with
        | error e => simp [hpa, Except.mapError] at hp
        | ok a =>
          simp [hpa, Except.mapError, pure, Except.pure] at hp
          exact ⟨a, hp.symm⟩
      · right
        have he' : Ipv4.endsInNumber (String.ofList asc) = false := by simpa using he
        simp only [he', Bool.false_eq_true, ite_false, pure, Except.pure, Except.ok.injEq] at hp
        obtain ⟨hascii, hlow, hne⟩ := domainToAscii_ok_props _ _ hd
        have hforb : ∀ c ∈ asc, Host.isForbiddenDomainCodePoint c = false := by
          simpa [List.any_eq_false] using hf'
        refine ⟨asc, hp.symm, ?_, hlow, hne, hf', he'⟩
        intro c hc
        refine ⟨hascii c hc, ?_⟩
        intro hcp
        have := hforb c hc
        rw [hcp] at this
        revert this
        decide

private theorem parseOpaque_ok (input : List Char) (h : Host) (hp : Host.parseOpaque input = .ok h) :
    h = .empty ∨ ∃ t, h = .opaqueHost t ∧ input ≠ [] := by
  by_cases hnil : input = []
  · left
    subst hnil
    simp only [Host.parseOpaque, Except.ok.injEq] at hp
    exact hp.symm
  right
  rw [parseOpaque_of_ne_nil input hnil] at hp
  by_cases hany : input.any Host.isForbiddenHostCodePoint = true
  · simp [hany] at hp
  · have hany' : input.any Host.isForbiddenHostCodePoint = false := by simpa using hany
    simp only [hany', Bool.false_eq_true, ite_false, Except.ok.injEq] at hp
    exact ⟨_, hp.symm, hnil⟩

theorem parse_serialize_of_parse (input : String) (isOpaque : Bool) (h : Host)
    (hp : Host.parse input isOpaque = .ok h) :
    Host.parse (Host.serialize h) isOpaque = .ok h := by
  unfold Host.parse at hp
  by_cases hbr : ∃ rest, input.toList = '[' :: rest
  · obtain ⟨rest, hrest⟩ := hbr
    rw [hrest] at hp
    unfold Host.parseChars at hp
    by_cases hlast : rest.getLast? = some ']'
    · simp only [hlast, ite_true] at hp
      cases hp6 : Host.Ipv6.parse (String.ofList rest.dropLast) with
      | error e => simp [hp6] at hp
      | ok a =>
        simp [hp6] at hp
        subst hp
        exact parse_serialize_ipv6 a isOpaque
    · simp [hlast] at hp
  · have hnb : ∀ rest, input.toList ≠ '[' :: rest := fun rest e => hbr ⟨rest, e⟩
    rw [parseChars_nonBracket _ _ hnb] at hp
    by_cases hop : isOpaque = true
    · subst hop
      simp only [ite_true] at hp
      rcases parseOpaque_ok _ _ hp with rfl | ⟨t, rfl, hne⟩
      · simp [Host.parse, Host.serialize, Host.parseChars, Host.parseOpaque]
      · have := parse_serialize_opaque input.toList t hne hp
        simpa [Host.parse, Host.serialize] using this
    · have hf : isOpaque = false := by simpa using hop
      subst hf
      simp only [Bool.false_eq_true, ite_false] at hp
      rcases parseDomain_cases _ _ hp with ⟨a, rfl⟩ | ⟨asc, rfl, hascii, hlow, hne, hforb, he⟩
      · exact parse_serialize_ipv4 a
      · have hl : (Host.serialize (.domain (String.ofList asc))).toList = asc := by
          simp [Host.serialize]
        have hfa : ∀ c ∈ asc, Host.isForbiddenDomainCodePoint c = false := by
          simpa [List.any_eq_false] using hforb
        have hnb2 : ∀ rest, asc ≠ '[' :: rest := by
          intro rest e
          have := hfa '[' (by rw [e]; simp)
          revert this
          decide
        unfold Host.parse
        rw [hl, parseChars_nonBracket _ _ hnb2]
        simp only [Bool.false_eq_true, ite_false]
        rw [parseDomain_stable asc hascii hlow hne hforb]
        simp [he]

theorem serialize_parse_serialize (input : String) (isOpaque : Bool) (h : Host)
    (hp : Host.parse input isOpaque = .ok h) :
    ∃ h', Host.parse (Host.serialize h) isOpaque = .ok h' ∧
      Host.serialize h' = Host.serialize h :=
  ⟨h, parse_serialize_of_parse input isOpaque h hp, rfl⟩

end Urllib.Host
