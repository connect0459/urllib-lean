import Urllib.Punycode

namespace Urllib.Punycode

/-- Every code point of the string is below 128. -/
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

private theorem encodeInsertions_ascii : ∀ (plan current : List (Nat × Nat)) (n i bias : Nat),
    AllAscii (encodeInsertions current n i bias plan)
  | [], _, _, _, _ => allAscii_nil
  | item :: rest, current, n, i, bias => by
    unfold encodeInsertions
    exact allAscii_append (encodeIntegerFrom_ascii _ _ _) (encodeInsertions_ascii rest _ _ _ _)

private theorem ofNat_ascii : ∀ n, n < 128 → (Char.ofNat n).toNat < 128 := by
  decide

theorem encode_isAscii (input : String) : IsAscii (encode input) := by
  unfold IsAscii encode
  rw [String.toList_ofList]
  apply allAscii_append
  · split
    · exact allAscii_nil
    · apply allAscii_append
      · intro c hc
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
        have := (List.mem_filter.mp hx).2
        exact ofNat_ascii x.1 (by simpa using this)
      · intro c hc
        cases hc with
        | head => decide
        | tail _ h => cases h
  · exact encodeInsertions_ascii _ _ _ _ _

private theorem charToDigit_digitToChar : ∀ d, d < 36 → charToDigit? (digitToChar d) = some d := by
  decide

private theorem digit_weight_identity (i w t r c d q : Nat) (hq : q = t + r + c * d) :
    i + (t + r) * w + d * (w * c) = i + q * w := by
  subst hq
  rw [Nat.add_mul (t + r) (c * d) w, Nat.mul_comm w c, ← Nat.mul_assoc, Nat.mul_comm d c]
  omega

theorem decodeInteger_encodeIntegerFrom (bias : Nat) :
    ∀ q k (rest : List Char) i w,
      decodeInteger bias (encodeIntegerFrom bias k q ++ rest) i w k = .ok (i + q * w, rest) := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro k rest i w
    have h1 := one_le_threshold k bias
    have h2 := threshold_le k bias
    rw [encodeIntegerFrom]
    split
    · rename_i hq
      rw [List.cons_append, List.nil_append, decodeInteger, charToDigit_digitToChar q (by omega)]
      simp [hq]
    · rename_i hq
      have hmod : (q - threshold k bias) % (base - threshold k bias) < base - threshold k bias :=
        Nat.mod_lt _ (by unfold base; omega)
      have hdiv := Nat.mod_add_div (q - threshold k bias) (base - threshold k bias)
      have hlt : (q - threshold k bias) / (base - threshold k bias) < q :=
        Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
      rw [List.cons_append, decodeInteger,
        charToDigit_digitToChar _ (by unfold base at hmod ⊢; omega)]
      have hnot : ¬ (threshold k bias + (q - threshold k bias) % (base - threshold k bias)
          < threshold k bias) := by omega
      simp only [hnot, ite_false]
      rw [ih _ hlt]
      congr 2
      exact digit_weight_identity i w (threshold k bias)
        ((q - threshold k bias) % (base - threshold k bias)) (base - threshold k bias)
        ((q - threshold k bias) / (base - threshold k bias)) q (by omega)

/-- The original positions of the items are strictly increasing. -/
def SortedIdx (l : List (Nat × Nat)) : Prop := l.Pairwise (fun a b => a.2 < b.2)

theorem insertAt_perm {α : Type} (xs : List α) (i : Nat) (x : α) :
    (insertAt xs i x).Perm (x :: xs) := by
  unfold insertAt
  have := List.perm_middle (a := x) (l₁ := xs.take i) (l₂ := xs.drop i)
  rwa [List.take_append_drop] at this

private theorem map_insertAt {α β : Type} (f : α → β) (xs : List α) (i : Nat) (x : α) :
    (insertAt xs i x).map f = insertAt (xs.map f) i (f x) := by
  simp [insertAt, List.map_take, List.map_drop]

theorem insertionPosition_cons (b : Nat × Nat) (l : List (Nat × Nat)) (it : Nat × Nat) :
    insertionPosition (b :: l) it =
      (if b.2 < it.2 then 1 else 0) + insertionPosition l it := by
  unfold insertionPosition
  rw [List.filter_cons]
  by_cases h : b.2 < it.2 <;> simp [h]; omega

private theorem insertionPosition_eq_zero (l : List (Nat × Nat)) (it : Nat × Nat)
    (h : ∀ y ∈ l, it.2 < y.2) : insertionPosition l it = 0 := by
  unfold insertionPosition
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro y hy
  have := h y hy
  simp; omega

private theorem insert_facts : ∀ (cur : List (Nat × Nat)) (it : Nat × Nat),
    SortedIdx cur → (∀ x ∈ cur, x.2 ≠ it.2) →
    SortedIdx (insertAt cur (insertionPosition cur it) it) ∧
    insertionPosition cur it ≤ cur.length ∧
    (∀ x ∈ cur.take (insertionPosition cur it), x.2 < it.2) := by
  intro cur it
  induction cur with
  | nil =>
    intro _ _
    have : insertionPosition [] it = 0 := by simp [insertionPosition]
    simp [this, insertAt, SortedIdx]
  | cons b l ih =>
    intro hsorted hne
    unfold SortedIdx at hsorted
    rw [List.pairwise_cons] at hsorted
    obtain ⟨hb, hl⟩ := hsorted
    have hbne : b.2 ≠ it.2 := hne b (by simp)
    have hlne : ∀ x ∈ l, x.2 ≠ it.2 := fun x hx => hne x (by simp [hx])
    obtain ⟨ih1, ih2, ih3⟩ := ih hl hlne
    by_cases h : b.2 < it.2
    · rw [insertionPosition_cons]
      simp only [h, ite_true]
      rw [Nat.add_comm 1]
      refine ⟨?_, by simp; omega, ?_⟩
      · show SortedIdx (b :: insertAt l (insertionPosition l it) it)
        unfold SortedIdx
        rw [List.pairwise_cons]
        refine ⟨fun y hy => ?_, ih1⟩
        have := (insertAt_perm l (insertionPosition l it) it).mem_iff.mp hy
        rcases List.mem_cons.mp this with rfl | hy'
        · exact h
        · exact hb y hy'
      · intro x hx
        simp only [List.take_succ_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact h
        · exact ih3 x hx
    · have hgt : it.2 < b.2 := by omega
      have hz : insertionPosition l it = 0 :=
        insertionPosition_eq_zero l it (fun y hy => by have := hb y hy; omega)
      rw [insertionPosition_cons]
      simp only [h, ite_false, hz, Nat.zero_add]
      refine ⟨?_, by simp, by simp⟩
      show SortedIdx (it :: b :: l)
      unfold SortedIdx
      rw [List.pairwise_cons]
      refine ⟨fun y hy => ?_, ?_⟩
      · rcases List.mem_cons.mp hy with rfl | hy'
        · exact hgt
        · have := hb y hy'; omega
      · exact List.pairwise_cons.mpr ⟨hb, hl⟩

private theorem pos_ge (cur : List (Nat × Nat)) (it : Nat × Nat) (i : Nat) (hi : i ≤ cur.length)
    (h : ∀ y ∈ cur.take i, y.2 < it.2) : i ≤ insertionPosition cur it := by
  unfold insertionPosition
  have hall : (cur.take i).filter (fun x => decide (x.2 < it.2)) = cur.take i := by
    rw [List.filter_eq_self]
    intro y hy
    simpa using h y hy
  have hlen : (cur.take i).length = i := by simp; omega
  calc i = ((cur.take i).filter (fun x => decide (x.2 < it.2))).length := by rw [hall, hlen]
    _ ≤ (cur.filter (fun x => decide (x.2 < it.2))).length :=
      List.Sublist.length_le (List.Sublist.filter _ (List.take_sublist i cur))

private theorem mix_div_mod (a size pos : Nat) (hpos : pos < size) :
    (a * size + pos) / size = a ∧ (a * size + pos) % size = pos := by
  have hsize : 0 < size := by omega
  have e : a * size + pos = pos + a * size := Nat.add_comm _ _
  rw [e, Nat.add_mul_div_right _ _ hsize, Nat.add_mul_mod_self_right]
  exact ⟨by rw [Nat.div_eq_of_lt hpos]; simp, Nat.mod_eq_of_lt hpos⟩

theorem encodeIntegerFrom_ne_nil (bias k q : Nat) : encodeIntegerFrom bias k q ≠ [] := by
  rw [encodeIntegerFrom]
  split <;> simp

private theorem decodeLoop_step (f : Nat) (c : Char) (cs : List Char) (n i bias : Nat) (output : List Nat)
    (i' : Nat) (rest : List Char)
    (hdec : decodeInteger bias (c :: cs) i 1 base = .ok (i', rest)) :
    decodeLoop (f + 1) (c :: cs) n i bias output =
      if Nat.isValidChar (n + i' / (output.length + 1)) then
        decodeLoop f rest (n + i' / (output.length + 1)) (i' % (output.length + 1) + 1)
          (adapt (i' - i) (output.length + 1) (i == 0))
          (insertAt output (i' % (output.length + 1)) (n + i' / (output.length + 1)))
      else .error .invalidCodePoint := by
  rw [decodeLoop]
  · simp only [hdec]
    rfl
  · intro h
    cases h

/-- An insertion plan is well formed when its items have distinct positions and are strictly ordered by code point, then by position. -/
def PlanOk (plan : List (Nat × Nat)) : Prop :=
  plan.Pairwise (fun a b => a.2 ≠ b.2 ∧ (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)))

private def Inv (cur : List (Nat × Nat)) (n i : Nat) (plan : List (Nat × Nat)) : Prop :=
  i ≤ cur.length ∧ (∀ x ∈ plan, n ≤ x.1) ∧
  (i = 0 ∨ ∃ last, (∀ y ∈ cur.take i, y.2 ≤ last) ∧ ∀ x ∈ plan, x.1 = n → last < x.2)

private def finalList (cur plan : List (Nat × Nat)) : List (Nat × Nat) :=
  plan.foldl (fun c it => insertAt c (insertionPosition c it) it) cur

private theorem take_insertAt (cur : List (Nat × Nat)) (it : Nat × Nat) (pos : Nat) (h : pos ≤ cur.length) :
    (insertAt cur pos it).take (pos + 1) = cur.take pos ++ [it] := by
  unfold insertAt
  rw [List.take_append]
  have h1 : (cur.take pos).length = pos := by simp; omega
  rw [h1, List.take_of_length_le (by omega)]
  simp

theorem length_insertAt {α : Type} (xs : List α) (i : Nat) (x : α) :
    (insertAt xs i x).length = xs.length + 1 := by
  rw [(insertAt_perm xs i x).length_eq]; simp

private theorem decodeLoop_encodeInsertions : ∀ (plan cur : List (Nat × Nat)) (n i bias fuel : Nat),
    SortedIdx cur → Inv cur n i plan → PlanOk plan →
    (∀ x ∈ plan, ∀ y ∈ cur, x.2 ≠ y.2) → (∀ x ∈ plan, Nat.isValidChar x.1) →
    (encodeInsertions cur n i bias plan).length ≤ fuel →
    decodeLoop fuel (encodeInsertions cur n i bias plan) n i bias (cur.map Prod.fst) =
      .ok ((finalList cur plan).map Prod.fst) := by
  intro plan
  induction plan with
  | nil =>
    intro cur n i bias fuel _ _ _ _ _ _
    simp [encodeInsertions, decodeLoop, finalList]
  | cons it rest ih =>
    intro cur n i bias fuel hsorted hinv hplan hnodup hvalid hfuel
    obtain ⟨hi_le, hn_le, hlast⟩ := hinv
    have hit_n : n ≤ it.1 := hn_le it (by simp)
    have hitne : ∀ x ∈ cur, x.2 ≠ it.2 := fun x hx => (hnodup it (by simp) x hx).symm
    obtain ⟨hsort', hposle, htake⟩ := insert_facts cur it hsorted hitne
    obtain ⟨hit_plan, hrest_plan⟩ := List.pairwise_cons.mp hplan
    have hdelta_ok : i ≤ (it.1 - n) * (cur.length + 1) + insertionPosition cur it := by
      by_cases hlt : n < it.1
      · have : cur.length + 1 ≤ (it.1 - n) * (cur.length + 1) :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      · have heq : it.1 = n := by omega
        simp only [heq, Nat.sub_self, Nat.zero_mul, Nat.zero_add]
        rcases hlast with h0 | ⟨last, hl1, hl2⟩
        · omega
        · exact pos_ge cur it i hi_le (fun y hy => by have := hl1 y hy; have := hl2 it (by simp) heq; omega)
    generalize hpos : insertionPosition cur it = pos at *
    generalize hsize : cur.length + 1 = size at *
    obtain ⟨delta, hdelta⟩ : ∃ delta, delta = (it.1 - n) * size + pos - i := ⟨_, rfl⟩
    have hsum : i + delta = (it.1 - n) * size + pos := by omega
    have hE : encodeInsertions cur n i bias (it :: rest) =
        encodeIntegerFrom bias base delta ++
          encodeInsertions (insertAt cur pos it) it.1 (pos + 1) (adapt delta size (i == 0)) rest := by
      rw [encodeInsertions, hdelta, ← hsize, ← hpos]
    generalize hE' : encodeInsertions (insertAt cur pos it) it.1 (pos + 1)
      (adapt delta size (i == 0)) rest = E' at hE
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (encodeIntegerFrom_ne_nil bias base delta)
    rw [hE, hcs, List.cons_append] at hfuel ⊢
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hdec := decodeInteger_encodeIntegerFrom bias delta base E' i 1
    rw [hcs, List.cons_append] at hdec
    rw [decodeLoop_step f c (cs ++ E') n i bias (cur.map Prod.fst) (i + delta * 1) E' hdec]
    have hlenmap : (cur.map Prod.fst).length + 1 = size := by simp [hsize]
    have hi' : i + delta * 1 = (it.1 - n) * size + pos := by rw [Nat.mul_one]; exact hsum
    have hposlt : pos < size := by omega
    obtain ⟨hdiv, hmod⟩ := mix_div_mod (it.1 - n) size pos hposlt
    have hnn : n + (it.1 - n) = it.1 := by omega
    have hadapt : i + delta * 1 - i = delta := by omega
    have hv := hvalid it (by simp)
    rw [hlenmap, hi', hdiv, hmod, hnn, ← hi', hadapt]
    simp only [hv, ite_true]
    have hmap : insertAt (cur.map Prod.fst) pos it.1 = (insertAt cur pos it).map Prod.fst :=
      (map_insertAt Prod.fst cur pos it).symm
    rw [hmap]
    have hfinal : finalList cur (it :: rest) = finalList (insertAt cur pos it) rest := by
      rw [← hpos]; rfl
    rw [hfinal, ← hE']
    refine ih (insertAt cur pos it) it.1 (pos + 1) (adapt delta size (i == 0)) f hsort' ?_
      hrest_plan ?_ (fun x hx => hvalid x (by simp [hx])) ?_
    · refine ⟨by rw [length_insertAt]; omega,
        fun x hx => by rcases (hit_plan x hx).2 with h | ⟨h, _⟩ <;> omega, Or.inr ⟨it.2, ?_, ?_⟩⟩
      · intro y hy
        rw [take_insertAt cur it pos (by omega)] at hy
        rcases List.mem_append.mp hy with hy | hy
        · have := htake y hy; omega
        · have : y = it := by simpa using hy
          subst this; exact Nat.le_refl _
      · intro x hx hx1
        rcases (hit_plan x hx).2 with h | ⟨_, h⟩
        · omega
        · exact h
    · intro x hx y hy
      have := (insertAt_perm cur pos it).mem_iff.mp hy
      rcases List.mem_cons.mp this with rfl | hy'
      · exact (hit_plan x hx).1.symm
      · exact hnodup x (by simp [hx]) y hy'
    · rw [← hE'] at hfuel
      simp at hfuel
      omega

private theorem finalList_facts : ∀ (plan cur : List (Nat × Nat)),
    SortedIdx cur → (∀ x ∈ plan, ∀ y ∈ cur, x.2 ≠ y.2) → PlanOk plan →
    SortedIdx (finalList cur plan) ∧ (finalList cur plan).Perm (cur ++ plan) := by
  intro plan
  induction plan with
  | nil =>
    intro cur hs _ _
    exact ⟨hs, by simp [finalList]⟩
  | cons it rest ih =>
    intro cur hs hnodup hplan
    obtain ⟨hit_plan, hrest_plan⟩ := List.pairwise_cons.mp hplan
    have hitne : ∀ x ∈ cur, x.2 ≠ it.2 := fun x hx => (hnodup it (by simp) x hx).symm
    obtain ⟨hsort', _, _⟩ := insert_facts cur it hs hitne
    have hfinal : finalList cur (it :: rest) =
        finalList (insertAt cur (insertionPosition cur it) it) rest := rfl
    rw [hfinal]
    have hnodup' : ∀ x ∈ rest, ∀ y ∈ insertAt cur (insertionPosition cur it) it, x.2 ≠ y.2 := by
      intro x hx y hy
      have := (insertAt_perm cur (insertionPosition cur it) it).mem_iff.mp hy
      rcases List.mem_cons.mp this with rfl | hy'
      · exact (hit_plan x hx).1.symm
      · exact hnodup x (by simp [hx]) y hy'
    obtain ⟨ih1, ih2⟩ := ih _ hsort' hnodup' hrest_plan
    refine ⟨ih1, ih2.trans ?_⟩
    have h1 : (insertAt cur (insertionPosition cur it) it ++ rest).Perm (it :: cur ++ rest) :=
      (insertAt_perm _ _ _).append_right rest
    exact h1.trans (by simpa using (List.perm_middle (a := it) (l₁ := cur) (l₂ := rest)).symm)

theorem eq_of_sortedIdx_perm {l₁ l₂ : List (Nat × Nat)} (h₁ : SortedIdx l₁) (h₂ : SortedIdx l₂)
    (hp : l₁.Perm l₂) : l₁ = l₂ := by
  unfold SortedIdx at h₁ h₂
  exact List.Perm.eq_of_pairwise (le := fun (a b : Nat × Nat) => a.2 < b.2)
    (fun a b _ _ hab hba => by omega) h₁ h₂ hp

theorem sortedIdx_zipIdx (T : List Nat) : SortedIdx T.zipIdx := by
  unfold SortedIdx
  have h := List.pairwise_lt_range' (s := 0) (n := T.length)
  rw [← List.zipIdx_map_snd 0 T] at h
  exact List.pairwise_map.mp h

theorem itemLe_trans : ∀ a b c : Nat × Nat, itemLe a b → itemLe b c → itemLe a c := by
  intro a b c h1 h2
  unfold itemLe at *
  simp at *
  omega

theorem itemLe_total : ∀ a b : Nat × Nat, (itemLe a b || itemLe b a) = true := by
  intro a b
  unfold itemLe
  simp
  omega

theorem basic_plan_perm (T : List Nat) : (basicItems T ++ planOf T).Perm T.zipIdx := by
  unfold basicItems planOf
  have h1 := List.mergeSort_perm (T.zipIdx.filter (fun x => decide (128 ≤ x.1))) (fun a b => itemLe a b)
  have h2 := List.filter_append_perm (fun (x : Nat × Nat) => decide (x.1 < 128)) T.zipIdx
  have h3 : T.zipIdx.filter (fun x => !decide (x.1 < 128)) =
      T.zipIdx.filter (fun x => decide (128 ≤ x.1)) := by
    apply List.filter_congr
    intro x _
    by_cases h : x.1 < 128
    · simp [h]
    · simp [h, (by omega : 128 ≤ x.1)]
  rw [h3] at h2
  exact (h1.append_left _).trans h2

theorem planOf_ok (T : List Nat) : PlanOk (planOf T) := by
  unfold PlanOk
  have hsorted := List.pairwise_mergeSort (le := fun a b => itemLe a b) itemLe_trans itemLe_total
    (T.zipIdx.filter (fun x => decide (128 ≤ x.1)))
  have hI := sortedIdx_zipIdx T
  unfold SortedIdx at hI
  have hne : (T.zipIdx.filter (fun x => decide (128 ≤ x.1))).Pairwise (fun a b => a.2 ≠ b.2) :=
    (hI.sublist (List.filter_sublist)).imp (fun h => by omega)
  have hne' : (planOf T).Pairwise (fun a b => a.2 ≠ b.2) := by
    unfold planOf
    exact (List.Perm.pairwise_iff (R := fun (a b : Nat × Nat) => a.2 ≠ b.2) (fun h => Ne.symm h)
      (List.mergeSort_perm _ _)).mpr hne
  unfold planOf at hne' ⊢
  refine (hne'.and hsorted).imp ?_
  intro a b ⟨hab, hle⟩
  refine ⟨hab, ?_⟩
  unfold itemLe at hle
  simp at hle
  omega


private theorem span_loop_all {α : Type} (p : α → Bool) : ∀ (l acc : List α),
    (∀ x ∈ l, p x = true) → List.span.loop p l acc = (acc.reverse ++ l, []) := by
  intro l
  induction l with
  | nil => intro acc _; simp [List.span.loop]
  | cons a l ih =>
    intro acc h
    have ha : p a = true := h a (by simp)
    rw [List.span.loop, ha]
    simp only
    rw [ih (a :: acc) (fun x hx => h x (by simp [hx]))]
    simp

private theorem span_loop_stop {α : Type} (p : α → Bool) : ∀ (l acc r : List α) (y : α),
    (∀ x ∈ l, p x = true) → p y = false →
    List.span.loop p (l ++ y :: r) acc = (acc.reverse ++ l, y :: r) := by
  intro l
  induction l with
  | nil => intro acc r y _ hy; simp [List.span.loop, hy]
  | cons a l ih =>
    intro acc r y h hy
    have ha : p a = true := h a (by simp)
    rw [List.cons_append, List.span.loop, ha]
    simp only
    rw [ih (a :: acc) r y (fun x hx => h x (by simp [hx])) hy]
    simp

private theorem span_stop {α : Type} (p : α → Bool) (l r : List α) (y : α)
    (h : ∀ x ∈ l, p x = true) (hy : p y = false) :
    (l ++ y :: r).span p = (l, y :: r) := by
  unfold List.span
  rw [span_loop_stop p l [] r y h hy]
  simp

private theorem span_all {α : Type} (p : α → Bool) (l : List α) (h : ∀ x ∈ l, p x = true) :
    l.span p = (l, []) := by
  unfold List.span
  rw [span_loop_all p l [] h]
  simp

private theorem digitToChar_ne_dash : ∀ d, d < 36 → digitToChar d ≠ '-' := by
  decide

private theorem encodeIntegerFrom_ne_dash (bias : Nat) : ∀ q k, ∀ c ∈ encodeIntegerFrom bias k q, c ≠ '-' := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro k c hc
    rw [encodeIntegerFrom] at hc
    have h1 := one_le_threshold k bias
    have h2 := threshold_le k bias
    split at hc
    · simp only [List.mem_singleton] at hc
      subst hc
      exact digitToChar_ne_dash q (by omega)
    · rcases List.mem_cons.mp hc with rfl | hc
      · apply digitToChar_ne_dash
        unfold base
        have : (q - threshold k bias) % (36 - threshold k bias) < 36 - threshold k bias :=
          Nat.mod_lt _ (by omega)
        omega
      · exact ih _ (by
          unfold base
          exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)) _ c hc

theorem encodeInsertions_ne_dash : ∀ (plan cur : List (Nat × Nat)) (n i bias : Nat),
    ∀ c ∈ encodeInsertions cur n i bias plan, c ≠ '-'
  | [], _, _, _, _ => by simp [encodeInsertions]
  | it :: rest, cur, n, i, bias => by
    intro c hc
    unfold encodeInsertions at hc
    rcases List.mem_append.mp hc with h | h
    · exact encodeIntegerFrom_ne_dash _ _ _ c h
    · exact encodeInsertions_ne_dash rest _ _ _ _ c h

private theorem ofNat_toNat_basic : ∀ n, n < 128 → (Char.ofNat n).toNat = n := by
  decide

private theorem validChar_toNat (c : Char) : Nat.isValidChar c.toNat := by
  exact c.valid

private theorem decode_prefixed (B ext : List Char) (hB : ∀ c ∈ B, c.toNat < 128)
    (hext : ∀ c ∈ ext, c ≠ '-') (out : List Nat)
    (h : decodeLoop ext.length ext initialN 0 initialBias (B.map Char.toNat) = .ok out) :
    decode (String.ofList (B ++ '-' :: ext)) = .ok (String.ofList (out.map Char.ofNat)) := by
  unfold decode
  rw [String.toList_ofList]
  have hrev : (B ++ '-' :: ext).reverse = ext.reverse ++ '-' :: B.reverse := by simp
  rw [hrev]
  have hspan := span_stop (fun c => c != delimiter) ext.reverse B.reverse '-'
    (fun x hx => by
      have := hext x (by simpa using hx)
      simpa [delimiter] using this)
    (by simp [delimiter])
  rw [hspan]
  have hany : (B.any fun x => decide (x.toNat ≥ 128)) = false := by
    simp only [List.any_eq_false, decide_eq_true_eq]
    intro c hc
    have := hB c hc
    omega
  simp only [List.reverse_reverse]
  rw [hany]
  simp only [Bool.false_eq_true, ite_false]
  rw [h]
  rfl

private theorem decode_unprefixed (ext : List Char) (hext : ∀ c ∈ ext, c ≠ '-') (out : List Nat)
    (h : decodeLoop ext.length ext initialN 0 initialBias [] = .ok out) :
    decode (String.ofList ext) = .ok (String.ofList (out.map Char.ofNat)) := by
  unfold decode
  rw [String.toList_ofList]
  have hspan := span_all (fun c => c != delimiter) ext.reverse
    (fun x hx => by
      have := hext x (by simpa using hx)
      simpa [delimiter] using this)
  rw [hspan]
  simp only [List.reverse_reverse, List.any_nil, Bool.false_eq_true, ite_false, List.map_nil]
  rw [h]
  rfl

private theorem decode_encode_core (T : List Nat) (hT : ∀ x ∈ T, Nat.isValidChar x) :
    decode (String.ofList
      ((if (basicItems T).isEmpty then []
        else (basicItems T).map (fun x => Char.ofNat x.1) ++ [delimiter]) ++
        encodeInsertions (basicItems T) initialN 0 initialBias (planOf T))) =
      .ok (String.ofList (T.map Char.ofNat)) := by
  have hI := sortedIdx_zipIdx T
  have hperm := basic_plan_perm T
  have hplanOk := planOf_ok T
  have hsortedB : SortedIdx (basicItems T) := by
    unfold SortedIdx basicItems at *
    exact hI.sublist List.filter_sublist
  have hmemPlan : ∀ x ∈ planOf T, 128 ≤ x.1 := by
    intro x hx
    unfold planOf at hx
    have := (List.mergeSort_perm _ _).mem_iff.mp hx
    simpa using (List.mem_filter.mp this).2
  have hmemI : ∀ x ∈ planOf T, x ∈ T.zipIdx := fun x hx =>
    hperm.mem_iff.mp (List.mem_append_right _ hx)
  have hvalid : ∀ x ∈ planOf T, Nat.isValidChar x.1 := fun x hx => by
    have := List.mem_map_of_mem (f := Prod.fst) (hmemI x hx)
    rw [List.zipIdx_map_fst] at this
    exact hT x.1 this
  have hdisj : ∀ x ∈ planOf T, ∀ y ∈ basicItems T, x.2 ≠ y.2 := by
    have hnd : ((basicItems T ++ planOf T).map Prod.snd).Nodup := by
      have h := hperm.map Prod.snd
      rw [List.zipIdx_map_snd] at h
      exact h.nodup_iff.mpr List.nodup_range'
    rw [List.map_append, List.nodup_append] at hnd
    intro x hx y hy e
    exact hnd.2.2 y.2 (List.mem_map_of_mem (f := Prod.snd) hy) x.2
      (List.mem_map_of_mem (f := Prod.snd) hx) e.symm
  have hinv : Inv (basicItems T) initialN 0 (planOf T) :=
    ⟨Nat.zero_le _, fun x hx => by have := hmemPlan x hx; unfold initialN; omega, Or.inl rfl⟩
  have hsim := decodeLoop_encodeInsertions (planOf T) (basicItems T) initialN 0 initialBias
    (encodeInsertions (basicItems T) initialN 0 initialBias (planOf T)).length hsortedB hinv
    hplanOk hdisj hvalid (Nat.le_refl _)
  have hfinal : finalList (basicItems T) (planOf T) = T.zipIdx := by
    obtain ⟨h1, h2⟩ := finalList_facts (planOf T) (basicItems T) hsortedB hdisj hplanOk
    exact eq_of_sortedIdx_perm h1 hI (h2.trans hperm)
  rw [hfinal, List.zipIdx_map_fst] at hsim
  have hnodash := encodeInsertions_ne_dash (planOf T) (basicItems T) initialN 0 initialBias
  have hbasic_lt : ∀ x ∈ basicItems T, x.1 < 128 := fun x hx => by
    have := (List.mem_filter.mp hx).2
    simpa using this
  by_cases hB : (basicItems T).isEmpty = true
  · have hnil : basicItems T = [] := List.isEmpty_iff.mp hB
    have hmap : (basicItems T).map Prod.fst = [] := by rw [hnil]; rfl
    rw [hmap] at hsim
    simp only [hB, ite_true, List.nil_append]
    exact decode_unprefixed _ hnodash T hsim
  · have hmapc : ((basicItems T).map (fun x => Char.ofNat x.1)).map Char.toNat =
        (basicItems T).map Prod.fst := by
      rw [List.map_map]
      apply List.map_congr_left
      intro x hx
      exact ofNat_toNat_basic x.1 (hbasic_lt x hx)
    rw [← hmapc] at hsim
    simp only [hB, Bool.false_eq_true, ite_false]
    have e : ((basicItems T).map (fun x => Char.ofNat x.1) ++ [delimiter]) ++
        encodeInsertions (basicItems T) initialN 0 initialBias (planOf T) =
        (basicItems T).map (fun x => Char.ofNat x.1) ++ '-' ::
          encodeInsertions (basicItems T) initialN 0 initialBias (planOf T) := by
      simp [delimiter]
    rw [e]
    refine decode_prefixed _ _ ?_ hnodash T hsim
    intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    rw [ofNat_toNat_basic x.1 (hbasic_lt x hx)]
    exact hbasic_lt x hx

theorem decode_encode (s : String) : decode (encode s) = .ok s := by
  have hT : ∀ x ∈ s.toList.map Char.toNat, Nat.isValidChar x := by
    intro x hx
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
    exact validChar_toNat c
  have h := decode_encode_core (s.toList.map Char.toNat) hT
  have hs : String.ofList ((s.toList.map Char.toNat).map Char.ofNat) = s := by
    simp [List.map_map, Function.comp_def]
  rw [hs] at h
  exact h

theorem zipIdx_filter_map_fst (p : Nat → Bool) : ∀ (T : List Nat) (k : Nat),
    ((T.zipIdx k).filter (fun x => p x.1)).map Prod.fst = T.filter p := by
  intro T
  induction T with
  | nil => intro k; simp
  | cons c T ih =>
    intro k
    rw [List.zipIdx_cons, List.filter_cons, List.filter_cons]
    by_cases h : p c = true <;> simp [h, ih]

theorem basicItems_map_fst (T : List Nat) :
    (basicItems T).map Prod.fst = T.filter (fun c => decide (c < 128)) := by
  unfold basicItems
  exact zipIdx_filter_map_fst (fun c => decide (c < 128)) T 0

theorem basic_chars (s : String) :
    (basicItems (s.toList.map Char.toNat)).map (fun x => Char.ofNat x.1) =
      s.toList.filter (fun c => decide (c.toNat < 128)) := by
  have h := basicItems_map_fst (s.toList.map Char.toNat)
  have h2 : (s.toList.map Char.toNat).filter (fun c => decide (c < 128)) =
      (s.toList.filter (fun c => decide (c.toNat < 128))).map Char.toNat := by
    rw [List.filter_map]; rfl
  rw [h2] at h
  calc (basicItems (s.toList.map Char.toNat)).map (fun x => Char.ofNat x.1)
      = ((basicItems (s.toList.map Char.toNat)).map Prod.fst).map Char.ofNat := by
        rw [List.map_map]; rfl
    _ = ((s.toList.filter (fun c => decide (c.toNat < 128))).map Char.toNat).map Char.ofNat := by
        rw [h]
    _ = s.toList.filter (fun c => decide (c.toNat < 128)) := by
        rw [List.map_map]
        have h3 : ∀ c : Char, Char.ofNat c.toNat = c := Char.ofNat_toNat
        simp only [Function.comp_def, h3, List.map_id']

theorem encode_basic_prefix (s : String) :
    ∃ ext : List Char, (∀ c ∈ ext, c ≠ '-') ∧
      (encode s).toList =
        (if (s.toList.filter (fun c => decide (c.toNat < 128))).isEmpty then []
          else s.toList.filter (fun c => decide (c.toNat < 128)) ++ ['-']) ++ ext := by
  refine ⟨encodeInsertions (basicItems (s.toList.map Char.toNat)) initialN 0 initialBias
    (planOf (s.toList.map Char.toNat)), encodeInsertions_ne_dash _ _ _ _ _, ?_⟩
  unfold encode
  rw [String.toList_ofList, ← basic_chars s]
  have hemp : ((basicItems (s.toList.map Char.toNat)).map (fun x => Char.ofNat x.1)).isEmpty =
      (basicItems (s.toList.map Char.toNat)).isEmpty := by simp
  rw [hemp]
  simp [delimiter]

theorem encode_basic_prefix_of_nonempty (s : String)
    (h : (s.toList.filter (fun c => decide (c.toNat < 128))) ≠ []) :
    ∃ ext : List Char, (∀ c ∈ ext, c ≠ '-') ∧
      (encode s).toList = s.toList.filter (fun c => decide (c.toNat < 128)) ++ '-' :: ext := by
  obtain ⟨ext, hext, he⟩ := encode_basic_prefix s
  refine ⟨ext, hext, ?_⟩
  have hne : (s.toList.filter (fun c => decide (c.toNat < 128))).isEmpty = false := by
    cases hb : s.toList.filter (fun c => decide (c.toNat < 128)) with
    | nil => exact absurd hb h
    | cons c cs => rfl
  rw [he]
  simp [hne]

theorem encode_no_delimiter_of_no_basic (s : String)
    (h : s.toList.filter (fun c => decide (c.toNat < 128)) = []) :
    ∀ c ∈ (encode s).toList, c ≠ '-' := by
  obtain ⟨ext, hext, he⟩ := encode_basic_prefix s
  rw [he]
  simp only [h, List.isEmpty_nil, ite_true, List.nil_append]
  exact hext

private theorem encodeIntegerFrom_digits (bias : Nat) :
    ∀ q k, ∀ c ∈ encodeIntegerFrom bias k q, ∃ d, d < 36 ∧ c = digitToChar d := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro k c hc
    rw [encodeIntegerFrom] at hc
    have h1 := one_le_threshold k bias
    have h2 := threshold_le k bias
    split at hc
    · cases hc with
      | head => exact ⟨q, by omega, rfl⟩
      | tail _ h => cases h
    · cases hc with
      | head =>
        refine ⟨_, ?_, rfl⟩
        unfold base
        have : (q - threshold k bias) % (36 - threshold k bias) < 36 - threshold k bias :=
          Nat.mod_lt _ (by omega)
        omega
      | tail _ h =>
        refine ih _ ?_ _ c h
        unfold base
        exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)

private theorem encodeInsertions_digits : ∀ (plan current : List (Nat × Nat)) (n i bias : Nat),
    ∀ c ∈ encodeInsertions current n i bias plan, ∃ d, d < 36 ∧ c = digitToChar d
  | [], _, _, _, _ => by
    intro c hc
    cases hc
  | item :: rest, current, n, i, bias => by
    intro c hc
    unfold encodeInsertions at hc
    rcases List.mem_append.mp hc with h | h
    · exact encodeIntegerFrom_digits _ _ _ c h
    · exact encodeInsertions_digits rest _ _ _ _ c h

/-- Every character of an encoding is a basic code point of the input, the delimiter, or a digit character. -/
theorem encode_char_cases (input : String) :
    ∀ c ∈ (encode input).toList,
      (c ∈ input.toList ∧ c.toNat < 128) ∨ c = '-' ∨ ∃ d, d < 36 ∧ c = digitToChar d := by
  intro c hc
  unfold encode at hc
  rw [String.toList_ofList] at hc
  rcases List.mem_append.mp hc with h | h
  · split at h
    · cases h
    · rcases List.mem_append.mp h with h | h
      · rw [basic_chars input] at h
        have hf := List.mem_filter.mp h
        left
        exact ⟨hf.1, by simpa using hf.2⟩
      · cases h with
        | head => right; left; rfl
        | tail _ h => cases h
  · right; right
    exact encodeInsertions_digits _ _ _ _ _ c h

end Urllib.Punycode
