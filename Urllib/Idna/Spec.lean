import Urllib.Idna
import Urllib.Punycode.Spec

namespace Urllib.Idna

open Urllib.Unicode

theorem splitDots_nil : splitDots [] = [[]] := rfl

theorem splitDots_cons (c : Char) (cs : List Char) :
    splitDots (c :: cs) =
      if c == '.' then [] :: splitDots cs
      else (c :: (splitDots cs).headD []) :: (splitDots cs).tail := by
  simp only [splitDots, List.foldr_cons]

theorem splitDots_ne_nil (cs : List Char) : splitDots cs ≠ [] := by
  induction cs with
  | nil => simp [splitDots_nil]
  | cons c cs _ =>
    rw [splitDots_cons]
    split <;> simp

theorem splitDots_eq_cons (cs : List Char) : ∃ l rest, splitDots cs = l :: rest := by
  cases h : splitDots cs with
  | nil => exact absurd h (splitDots_ne_nil cs)
  | cons l rest => exact ⟨l, rest, rfl⟩

theorem joinDots_cons_head (c : Char) (l : List Char) (rest : List (List Char)) :
    joinDots ((c :: l) :: rest) = c :: joinDots (l :: rest) := by
  cases rest <;> simp [joinDots]

theorem joinDots_splitDots (cs : List Char) : joinDots (splitDots cs) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨l, rest, h⟩ := splitDots_eq_cons cs
    rw [splitDots_cons, h]
    rw [h] at ih
    by_cases hc : (c == '.') = true
    · simp only [hc, ite_true, List.headD_cons, List.tail_cons]
      have : c = '.' := by simpa using hc
      subst this
      simp [joinDots]
      cases rest <;> simpa [joinDots] using ih
    · simp only [hc, Bool.false_eq_true, ite_false, List.headD_cons, List.tail_cons]
      rw [joinDots_cons_head, ih]

theorem not_mem_splitDots (cs : List Char) : ∀ l ∈ splitDots cs, '.' ∉ l := by
  induction cs with
  | nil =>
    intro l hl
    simp [splitDots_nil] at hl
    subst hl
    simp
  | cons c cs ih =>
    intro l hl
    obtain ⟨l0, rest, h⟩ := splitDots_eq_cons cs
    rw [splitDots_cons, h] at hl
    by_cases hc : (c == '.') = true
    · simp only [hc, ite_true, List.mem_cons] at hl
      rcases hl with rfl | hl
      · simp
      · exact ih l (by rw [h]; exact List.mem_cons.mpr hl)
    · simp only [hc, Bool.false_eq_true, ite_false, List.headD_cons, List.tail_cons, List.mem_cons] at hl
      have hcne : c ≠ '.' := by simpa using hc
      rcases hl with rfl | hl
      · intro hmem
        rcases List.mem_cons.mp hmem with e | hmem
        · exact hcne e.symm
        · exact ih l0 (by rw [h]; exact List.mem_cons_self) hmem
      · exact ih l (by rw [h]; exact List.mem_cons_of_mem _ hl)

theorem splitDots_of_no_dot (l : List Char) (h : '.' ∉ l) : splitDots l = [l] := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    have hc : c ≠ '.' := fun e => h (e ▸ List.mem_cons_self)
    have hl : '.' ∉ l := fun m => h (List.mem_cons_of_mem _ m)
    rw [splitDots_cons, ih hl]
    simp [hc]

theorem splitDots_append_dot (l : List Char) (cs : List Char) (h : '.' ∉ l) :
    splitDots (l ++ '.' :: cs) = l :: splitDots cs := by
  induction l with
  | nil => simp [splitDots_cons]
  | cons c l ih =>
    have hc : c ≠ '.' := fun e => h (e ▸ List.mem_cons_self)
    have hl : '.' ∉ l := fun m => h (List.mem_cons_of_mem _ m)
    rw [List.cons_append, splitDots_cons, ih hl]
    simp [hc]

theorem splitDots_joinDots (l : List Char) (rest : List (List Char))
    (h : ∀ x ∈ l :: rest, '.' ∉ x) : splitDots (joinDots (l :: rest)) = l :: rest := by
  induction rest generalizing l with
  | nil => simpa [joinDots] using splitDots_of_no_dot l (h l List.mem_cons_self)
  | cons l' rest ih =>
    simp only [joinDots]
    rw [splitDots_append_dot l _ (h l List.mem_cons_self)]
    rw [ih l' (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem combiningClass_ascii (c : Char) (h : c.toNat < 128) : combiningClass c = 0 := by
  unfold combiningClass
  have : c.toNat < 0x300 := by omega
  simp [this]

theorem decomposition_ascii (c : Char) (h : c.toNat < 128) : decomposition c = [] := by
  unfold decomposition
  have : c.toNat < 0xC0 := by omega
  simp [this]

theorem compose_ascii_right (a b : Char) (h : b.toNat < 128) : compose a b = none := by
  unfold compose
  have : b.toNat < 0x300 := by omega
  simp [this]

theorem reorder_go_ascii : ∀ (cs acc : List Char), (∀ c ∈ cs, c.toNat < 128) →
    reorder.go cs [] acc = acc ++ cs
  | [], acc, _ => by simp [reorder.go, reorder.flush]
  | c :: rest, acc, h => by
    have hc := h c List.mem_cons_self
    have hrest : ∀ x ∈ rest, x.toNat < 128 := fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [reorder.go, combiningClass_ascii c hc, beq_self_eq_true, ite_true]
    rw [reorder_go_ascii rest _ hrest]
    simp [reorder.flush]

theorem reorder_ascii (cs : List Char) (h : ∀ c ∈ cs, c.toNat < 128) : reorder cs = cs := by
  unfold reorder
  rw [reorder_go_ascii cs [] h]
  simp

theorem composeStep_ascii (state : ComposeState) (c : Char) (h : c.toNat < 128) :
    (composeStep state c).output = state.output.push c := by
  unfold composeStep
  cases hs : state.starter with
  | none => simp [composeStep.appendChar, combiningClass_ascii c h]
  | some p =>
    obtain ⟨i, st⟩ := p
    simp [compose_ascii_right _ _ h, composeStep.appendChar, combiningClass_ascii c h]

theorem composeStep_ascii_foldl (cs : List Char) (h : ∀ c ∈ cs, c.toNat < 128) :
    ∀ (state : ComposeState), (cs.foldl composeStep state).output.toList = state.output.toList ++ cs := by
  induction cs with
  | nil => intro state; simp
  | cons c cs ih =>
    intro state
    rw [List.foldl_cons, ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), composeStep_ascii state c (h c List.mem_cons_self)]
    simp

theorem decomposeChar_ascii (c : Char) (h : c.toNat < 128) : decomposeChar c = [c] := by
  simp [decomposeChar, decomposition_ascii c h]

theorem flatMap_decomposeChar_ascii : ∀ (cs : List Char), (∀ c ∈ cs, c.toNat < 128) →
    cs.flatMap decomposeChar = cs
  | [], _ => rfl
  | c :: rest, h => by
    rw [List.flatMap_cons, decomposeChar_ascii c (h c List.mem_cons_self),
      flatMap_decomposeChar_ascii rest (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

theorem nfc_ascii (cs : List Char) (h : ∀ c ∈ cs, c.toNat < 128) : nfc cs = cs := by
  unfold nfc composeAll
  rw [flatMap_decomposeChar_ascii cs h, reorder_ascii cs h]
  have := composeStep_ascii_foldl cs h { output := #[], starter := none, lastClass := 0 }
  simpa using this

/-- An ASCII code point that the mapping table keeps as is. -/
abbrev AsciiClean (c : Char) : Prop := c.toNat < 128 ∧ status c = .valid

private theorem ascii_char_cases (P : Char → Prop) (hP : ∀ n, n < 128 → P (Char.ofNat n)) (c : Char)
    (h : c.toNat < 128) : P c := by
  have : c = Char.ofNat c.toNat := (Char.ofNat_toNat c).symm
  rw [this]
  exact hP c.toNat h

theorem status_ascii (c : Char) (h : c.toNat < 128) :
    status c = .valid ∨ ∃ t, status c = .mapped t := by
  unfold status
  have : c.toNat < 0x80 := by omega
  simp only [this, ite_true]
  split
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

theorem mapChar_clean (c : Char) (h : AsciiClean c) : mapChar c = [c] := by
  unfold mapChar
  rw [h.2]

theorem flatMap_mapChar_clean : ∀ (cs : List Char), (∀ c ∈ cs, AsciiClean c) →
    cs.flatMap mapChar = cs
  | [], _ => rfl
  | c :: rest, h => by
    rw [List.flatMap_cons, mapChar_clean c (h c List.mem_cons_self),
      flatMap_mapChar_clean rest (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

theorem clean_toLower (c : Char) (h : AsciiClean c) : c.toLower = c := by
  refine ascii_char_cases (fun c => status c = .valid → c.toLower = c) ?_ c h.1 h.2
  decide

theorem digit_clean (d : Nat) (h : d < 36) : AsciiClean (Punycode.digitToChar d) := by
  revert h
  revert d
  decide

theorem validityErrors_no_dot (o : Options) (l : List Char) (h : validityErrors o l = []) : '.' ∉ l := by
  intro hm
  simp [validityErrors, List.append_eq_nil_iff, hm] at h

theorem validityErrors_no_ace (o : Options) (hh : o.checkHyphens = false) (l : List Char)
    (h : validityErrors o l = []) : (l.take 4 == acePrefix) = false := by
  cases hb : (l.take 4 == acePrefix) with
  | false => rfl
  | true => simp [validityErrors, List.append_eq_nil_iff, hh, hb] at h

theorem validityErrors_ascii_valid (o : Options) (l : List Char) (h : validityErrors o l = []) :
    ∀ c ∈ l, c.toNat < 128 → status c = .valid := by
  intro c hc hlt
  rcases status_ascii c hlt with hv | ⟨t, ht⟩
  · exact hv
  · exfalso
    simp [validityErrors, List.append_eq_nil_iff] at h
    have h5 := h.2.2.2.2.1 c hc
    rw [ht] at h5
    simp at h5

theorem convertLabel_validate (l : List Char) (h : (convertLabel l).2.1 = []) :
    (convertLabel l).2.2 = true := by
  by_cases h1 : (l.take 4 == acePrefix) = true
  · by_cases h2 : (l.any fun c => !isAscii c) = true
    · simp [convertLabel, h1, h2] at h
    · cases hd : Punycode.decode (String.ofList (l.drop 4)) with
      | error e => simp [convertLabel, h1, h2, hd] at h
      | ok dec => simp [convertLabel, h1, h2, hd]
  · simp [convertLabel, h1]

theorem convertLabel_ascii (l : List Char) (hn : (l.take 4 == acePrefix) = false) :
    convertLabel l = (l, [], true) := by
  simp [convertLabel, hn]

theorem acePrefix_length : acePrefix.length = 4 := rfl

theorem convertLabel_encodeLabel (l : List Char) (hA : l.all isAscii = false) :
    convertLabel (encodeLabel l) = (l, [], true) := by
  have hnot : ¬ (l.all isAscii = true) := by simp [hA]
  have hE : encodeLabel l = acePrefix ++ (Punycode.encode (String.ofList l)).toList := by
    unfold encodeLabel
    simp [hnot]
  rw [hE]
  have hasc : ∀ c ∈ (Punycode.encode (String.ofList l)).toList, c.toNat < 128 :=
    Punycode.encode_isAscii _
  have htake : (acePrefix ++ (Punycode.encode (String.ofList l)).toList).take 4 = acePrefix :=
    List.take_left' acePrefix_length
  have hdrop : (acePrefix ++ (Punycode.encode (String.ofList l)).toList).drop 4 =
      (Punycode.encode (String.ofList l)).toList :=
    List.drop_left' acePrefix_length
  have hany : ((acePrefix ++ (Punycode.encode (String.ofList l)).toList).any fun c => !isAscii c) = false := by
    simp only [List.any_append, Bool.or_eq_false_iff]
    constructor
    · decide
    · simp only [List.any_eq_false]
      intro c hc
      have := hasc c hc
      simp [isAscii, this]
  have hdec := Punycode.decode_encode (String.ofList l)
  have hne : l ≠ [] := by
    intro e
    simp [e] at hA
  simp only [convertLabel, htake, hdrop, hany, String.ofList_toList, hdec]
  simp [hA, hne]

theorem processConverted_labels (o : Options) (conv : List (List Char × List Error × Bool)) :
    (processConverted o conv).1 = conv.map (·.1) := by
  simp [processConverted, List.map_map, Function.comp_def]

theorem processConverted_errors_nil (o : Options) (conv : List (List Char × List Error × Bool))
    (h : (processConverted o conv).2 = []) :
    ∀ e ∈ conv, e.2.1 = [] ∧ (e.2.2 = true → e.1 ≠ [] → validityErrors o e.1 = []) := by
  intro e he
  obtain ⟨label, errors, validate⟩ := e
  simp only [processConverted, List.flatMap_eq_nil_iff, List.mem_map] at h
  have h' := h _ ⟨(label, errors, validate), he, rfl⟩
  simp only [List.append_eq_nil_iff] at h'
  refine ⟨h'.1.1, ?_⟩
  intro hv hne
  subst hv
  simpa [hne] using h'.1.2

theorem acePrefix_clean : ∀ c ∈ acePrefix, AsciiClean c := by decide

theorem digit_ne_dot : ∀ d, d < 36 → Punycode.digitToChar d ≠ '.' := by decide

theorem conv_facts (o : Options) (L : List (List Char))
    (herr : (processConverted o (L.map convertLabel)).2 = []) :
    ∀ e ∈ L.map convertLabel, e = (e.1, [], true) ∧ (e.1 = [] ∨ validityErrors o e.1 = []) := by
  intro e he
  have hall := processConverted_errors_nil o _ herr e he
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp he
  have hvalid := convertLabel_validate x hall.1
  refine ⟨Prod.ext rfl (Prod.ext hall.1 hvalid), ?_⟩
  by_cases hne : (convertLabel x).1 = []
  · exact Or.inl hne
  · exact Or.inr (hall.2 hvalid hne)

theorem encodeLabel_facts (o : Options) (hh : o.checkHyphens = false) (l : List Char)
    (hl : l = [] ∨ validityErrors o l = []) :
    '.' ∉ encodeLabel l ∧ (∀ c ∈ encodeLabel l, AsciiClean c) ∧
      convertLabel (encodeLabel l) = (l, [], true) := by
  by_cases hA : l.all isAscii = true
  · have hE : encodeLabel l = l := by simp [encodeLabel, hA]
    rw [hE]
    rcases hl with rfl | hv
    · refine ⟨by simp, by simp, ?_⟩
      exact convertLabel_ascii [] (by decide)
    · refine ⟨validityErrors_no_dot o l hv, ?_, convertLabel_ascii l (validityErrors_no_ace o hh l hv)⟩
      intro c hc
      have hlt : c.toNat < 128 := by
        have := List.all_eq_true.mp hA c hc
        simpa [isAscii] using this
      exact ⟨hlt, validityErrors_ascii_valid o l hv c hc hlt⟩
  · have hA' : l.all isAscii = false := by simpa using hA
    have hne : l ≠ [] := by
      intro e
      simp [e] at hA'
    have hv : validityErrors o l = [] := hl.resolve_left hne
    have hE : encodeLabel l = acePrefix ++ (Punycode.encode (String.ofList l)).toList := by
      unfold encodeLabel
      simp [hA]
    refine ⟨?_, ?_, convertLabel_encodeLabel l hA'⟩
    · rw [hE]
      intro hm
      rcases List.mem_append.mp hm with h | h
      · revert h
        decide
      · rcases Punycode.encode_char_cases _ _ h with ⟨hl', _⟩ | h2 | ⟨d, hd, hdc⟩
        · exact validityErrors_no_dot o l hv (by simpa using hl')
        · revert h2
          decide
        · exact digit_ne_dot d hd hdc.symm
    · rw [hE]
      intro c hc
      rcases List.mem_append.mp hc with h | h
      · exact acePrefix_clean c h
      · rcases Punycode.encode_char_cases _ _ h with ⟨hl', hlt⟩ | h2 | ⟨d, hd, hdc⟩
        · exact ⟨hlt, validityErrors_ascii_valid o l hv c (by simpa using hl') hlt⟩
        · subst h2
          decide
        · rw [hdc]
          exact digit_clean d hd

theorem mem_joinDots (c : Char) : ∀ (Ls : List (List Char)), c ∈ joinDots Ls →
    c = '.' ∨ ∃ l ∈ Ls, c ∈ l
  | [], h => by simp [joinDots] at h
  | [l], h => Or.inr ⟨l, List.mem_cons_self, by simpa [joinDots] using h⟩
  | l :: l' :: rest, h => by
    simp only [joinDots, List.mem_append, List.mem_cons] at h
    rcases h with h | h | h
    · exact Or.inr ⟨l, List.mem_cons_self, h⟩
    · exact Or.inl h
    · rcases mem_joinDots c (l' :: rest) h with h | ⟨x, hx, hc⟩
      · exact Or.inl h
      · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hc⟩

theorem toAsciiChars_ok (o : Options) (hv : o.verifyDnsLength = false) (d a : List Char)
    (h : toAsciiChars o d = .ok a) :
    (processConverted o ((splitDots (nfc (d.flatMap mapChar))).map convertLabel)).2 = [] ∧
      a = joinDots ((((splitDots (nfc (d.flatMap mapChar))).map convertLabel).map (·.1)).map encodeLabel) := by
  unfold toAsciiChars processLabels processMapped at h
  simp only [hv, Bool.false_eq_true, ite_false, List.append_nil] at h
  generalize List.map convertLabel (splitDots (nfc (List.flatMap mapChar d))) = conv at h ⊢
  by_cases he : (processConverted o conv).snd.isEmpty = true
  · simp only [he, ite_true] at h
    have h' := Except.ok.inj h
    refine ⟨List.isEmpty_iff.mp he, ?_⟩
    rw [← h', processConverted_labels]
  · have he' : (processConverted o conv).snd.isEmpty = false := by simpa using he
    simp only [he', Bool.false_eq_true, ite_false] at h
    cases h

theorem toAsciiChars_ok_clean (o : Options) (hh : o.checkHyphens = false) (hv : o.verifyDnsLength = false)
    (d a : List Char) (h : toAsciiChars o d = .ok a) : ∀ c ∈ a, AsciiClean c := by
  obtain ⟨herr, ha⟩ := toAsciiChars_ok o hv d a h
  have hfacts := conv_facts o _ herr
  intro c hc
  rw [ha] at hc
  rcases mem_joinDots c _ hc with rfl | ⟨l, hl, hcl⟩
  · decide
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hl
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hu
    exact (encodeLabel_facts o hh e.1 (hfacts e he).2).2.1 c hcl

theorem toAsciiChars_idempotent (o : Options) (hh : o.checkHyphens = false) (hv : o.verifyDnsLength = false)
    (d a : List Char) (h : toAsciiChars o d = .ok a) : toAsciiChars o a = .ok a := by
  have hclean := toAsciiChars_ok_clean o hh hv d a h
  obtain ⟨herr, ha⟩ := toAsciiChars_ok o hv d a h
  obtain ⟨conv, hconv⟩ : ∃ conv, (splitDots (nfc (d.flatMap mapChar))).map convertLabel = conv :=
    ⟨_, rfl⟩
  have hne : conv ≠ [] := by
    rw [← hconv]
    simpa using splitDots_ne_nil _
  rw [hconv] at herr ha
  have hfacts : ∀ e ∈ conv, e = (e.1, [], true) ∧ (e.1 = [] ∨ validityErrors o e.1 = []) := by
    rw [← hconv] at herr ⊢
    exact conv_facts o _ herr
  have hmap : nfc (a.flatMap mapChar) = a := by
    rw [flatMap_mapChar_clean a hclean]
    exact nfc_ascii a (fun c hc => (hclean c hc).1)
  obtain ⟨l1, rest, hlr⟩ : ∃ l1 rest, (conv.map (·.1)).map encodeLabel = l1 :: rest := by
    cases hc : (conv.map (·.1)).map encodeLabel with
    | nil => exact absurd (by simpa using hc) hne
    | cons l1 rest => exact ⟨l1, rest, rfl⟩
  have hnodots : ∀ x ∈ l1 :: rest, '.' ∉ x := by
    rw [← hlr]
    intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hu
    exact (encodeLabel_facts o hh e.1 (hfacts e he).2).1
  have hsplit : splitDots a = (conv.map (·.1)).map encodeLabel := by
    have : a = joinDots (l1 :: rest) := by rw [ha, hlr]
    rw [this, hlr]
    exact splitDots_joinDots l1 rest hnodots
  have hconv2 : (splitDots (nfc (a.flatMap mapChar))).map convertLabel = conv := by
    rw [hmap, hsplit, List.map_map, List.map_map]
    calc conv.map (convertLabel ∘ encodeLabel ∘ fun x => x.1) = conv.map id :=
          List.map_congr_left (fun e he => by
            simp only [Function.comp_apply, id]
            rw [(encodeLabel_facts o hh e.1 (hfacts e he).2).2.2]
            exact ((hfacts e he).1).symm)
      _ = conv := List.map_id _
  unfold toAsciiChars processLabels processMapped at h ⊢
  rw [hconv] at h
  rw [hconv2]
  exact h

theorem mem_joinDots_of_mem (c : Char) (l : List Char) :
    ∀ (Ls : List (List Char)), l ∈ Ls → c ∈ l → c ∈ joinDots Ls
  | [], h, _ => by simp at h
  | [x], h, hc => by
    have : l = x := by simpa using h
    subst this
    simpa [joinDots] using hc
  | x :: x' :: rest, h, hc => by
    simp only [joinDots, List.mem_append, List.mem_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl hc
    · exact Or.inr (Or.inr (mem_joinDots_of_mem c l (x' :: rest) h hc))

theorem contextJOk_go_ascii : ∀ (l before : List Char), (∀ c ∈ l, c.toNat < 128) →
    contextJOk.go before l = true
  | [], _, _ => by simp [contextJOk.go]
  | c :: after, before, h => by
    have hc := h c List.mem_cons_self
    have hj : (c == Char.ofNat 0x200C) = false ∧ (c == Char.ofNat 0x200D) = false :=
      ascii_char_cases (fun c => (c == Char.ofNat 0x200C) = false ∧ (c == Char.ofNat 0x200D) = false)
        (by decide) c hc
    simp only [contextJOk.go, hj.1, hj.2, Bool.false_eq_true, ite_false, Bool.true_and]
    exact contextJOk_go_ascii after _ (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem isRtlLabel_ascii (l : List Char) (h : ∀ c ∈ l, c.toNat < 128) : isRtlLabel l = false := by
  unfold isRtlLabel
  simp only [List.any_eq_false]
  intro c hc
  have := h c hc
  have : ¬ (0x590 ≤ c.toNat) := by omega
  simp [isRtl, this]

theorem validityErrors_clean (o : Options) (hh : o.checkHyphens = false) (hs : o.useStd3AsciiRules = false)
    (l : List Char) (hc : ∀ c ∈ l, AsciiClean c) (hdot : '.' ∉ l)
    (hace : (l.take 4 == acePrefix) = false) : validityErrors o l = [] := by
  have hasc : ∀ c ∈ l, c.toNat < 128 := fun c h => (hc c h).1
  have hmark : l.head?.any isMark = false := by
    cases l with
    | nil => rfl
    | cons c rest =>
      have : ¬ (0x300 ≤ c.toNat) := by
        have := hasc c List.mem_cons_self
        omega
      simp [isMark, this]
  have hj : contextJOk l = true := contextJOk_go_ascii l [] hasc
  simp [validityErrors, nfc_ascii l hasc, hh, hs, hace, hdot, hmark, hj]
  intro x hx
  rw [(hc x hx).2]

theorem processConverted_errors_nil_of (o : Options) (conv : List (List Char × List Error × Bool))
    (hconv : ∀ e ∈ conv, e.2.1 = [] ∧ (e.2.2 = true → e.1 ≠ [] → validityErrors o e.1 = []))
    (hbidi : (o.checkBidi && conv.any fun e => isRtlLabel e.1) = false) :
    (processConverted o conv).2 = [] := by
  simp only [processConverted, List.flatMap_eq_nil_iff, List.mem_map]
  rintro _ ⟨⟨label, errors, validate⟩, he, rfl⟩
  have h := hconv _ he
  simp only [List.append_eq_nil_iff]
  refine ⟨⟨h.1, ?_⟩, ?_⟩
  · by_cases hv : (validate && !label.isEmpty) = true
    · have hv' : validate = true ∧ label ≠ [] := by simpa using hv
      simp [hv, h.2 hv'.1 hv'.2]
    · simp [hv]
  · simp [hbidi]

theorem ace_prefix_false (l : List Char) (hx : 'x' ∉ l) : (l.take 4 == acePrefix) = false := by
  cases hb : (l.take 4 == acePrefix) with
  | false => rfl
  | true =>
    exfalso
    have htk : l.take 4 = acePrefix := by simpa using hb
    apply hx
    have : 'x' ∈ l.take 4 := by rw [htk]; decide
    exact List.mem_of_mem_take this

theorem toAsciiChars_ascii_fixed (o : Options) (hh : o.checkHyphens = false) (hv : o.verifyDnsLength = false)
    (hs : o.useStd3AsciiRules = false) (d : List Char) (hd : ∀ c ∈ d, AsciiClean c)
    (hx : ∀ c ∈ d, c ≠ 'x') : toAsciiChars o d = .ok d := by
  have hmap : nfc (d.flatMap mapChar) = d := by
    rw [flatMap_mapChar_clean d hd]
    exact nfc_ascii d (fun c hc => (hd c hc).1)
  have hlab : ∀ l ∈ splitDots d, ∀ c ∈ l, c ∈ d := by
    intro l hl c hc
    have := mem_joinDots_of_mem c l (splitDots d) hl hc
    rwa [joinDots_splitDots] at this
  have hace : ∀ l ∈ splitDots d, (l.take 4 == acePrefix) = false := fun l hl =>
    ace_prefix_false l (fun hm => hx 'x' (hlab l hl 'x' hm) rfl)
  have hconv : ∀ l ∈ splitDots d, convertLabel l = (l, [], true) := fun l hl =>
    convertLabel_ascii l (hace l hl)
  have hcm : (splitDots d).map convertLabel = (splitDots d).map (fun l => (l, ([] : List Error), true)) :=
    List.map_congr_left hconv
  have herr : (processConverted o ((splitDots d).map convertLabel)).2 = [] := by
    apply processConverted_errors_nil_of
    · intro e he
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
      rw [hconv l hl]
      refine ⟨rfl, fun _ hne => ?_⟩
      exact validityErrors_clean o hh hs l (fun c hc => hd c (hlab l hl c hc))
        (not_mem_splitDots d l hl) (hace l hl)
    · rw [hcm]
      have : (((splitDots d).map fun l => (l, ([] : List Error), true)).any fun e => isRtlLabel e.1) = false := by
        simp only [List.any_map, List.any_eq_false]
        intro l hl
        simpa using isRtlLabel_ascii l (fun c hc => (hd c (hlab l hl c hc)).1)
      simp [this]
  have hlabels : (processConverted o ((splitDots d).map convertLabel)).1 = splitDots d := by
    rw [processConverted_labels, hcm, List.map_map]
    have hid : ((fun x : List Char × List Error × Bool => x.1) ∘
        fun l : List Char => (l, ([] : List Error), true)) = id := rfl
    rw [hid, List.map_id]
  have henc : (splitDots d).map encodeLabel = splitDots d := by
    calc (splitDots d).map encodeLabel = (splitDots d).map id :=
          List.map_congr_left (fun l hl => by
            have hA : l.all isAscii = true := by
              simp only [List.all_eq_true]
              intro c hc
              simpa [isAscii] using (hd c (hlab l hl c hc)).1
            simp [encodeLabel, hA])
      _ = splitDots d := List.map_id _
  unfold toAsciiChars processLabels processMapped
  rw [hmap]
  simp only [hv, Bool.false_eq_true, ite_false, List.append_nil, herr, hlabels, henc, joinDots_splitDots]
  rfl

end Urllib.Idna
