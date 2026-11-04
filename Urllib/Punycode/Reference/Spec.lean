import Urllib.Punycode.Reference
import Urllib.Punycode.Spec

namespace Urllib.Punycode
private structure CState where
  n : Nat
  i : Nat
  bias : Nat
  j : Nat

private def closedStep (T : List Nat) (b : Nat) (st : CState) (it : Nat × Nat) : List Char × CState :=
  let size := b + st.j + 1
  let pos := ((T.take it.2).filter (fun c => decide (c ≤ it.1))).length
  let delta := (it.1 - st.n) * size + pos - st.i
  (encodeIntegerFrom st.bias base delta, ⟨it.1, pos + 1, adapt delta size (st.i == 0), st.j + 1⟩)

private def closedOut (T : List Nat) (b : Nat) : CState → List (Nat × Nat) → List Char
  | _, [] => []
  | st, it :: rest => (closedStep T b st it).1 ++ closedOut T b (closedStep T b st it).2 rest

private def closedEnd (T : List Nat) (b : Nat) : CState → List (Nat × Nat) → CState
  | st, [] => st
  | st, it :: rest => closedEnd T b (closedStep T b st it).2 rest

private theorem closedOut_append (T : List Nat) (b : Nat) : ∀ (G R : List (Nat × Nat)) (st : CState),
    closedOut T b st (G ++ R) = closedOut T b st G ++ closedOut T b (closedEnd T b st G) R := by
  intro G
  induction G with
  | nil => intro R st; simp [closedOut, closedEnd]
  | cons it G ih =>
    intro R st
    simp only [List.cons_append, closedOut, closedEnd, ih, List.append_assoc]

private theorem closedEnd_append (T : List Nat) (b : Nat) : ∀ (G R : List (Nat × Nat)) (st : CState),
    closedEnd T b st (G ++ R) = closedEnd T b (closedEnd T b st G) R := by
  intro G
  induction G with
  | nil => intro R st; simp [closedEnd]
  | cons it G ih =>
    intro R st
    simp only [List.cons_append, closedEnd, ih]

private theorem zipIdx_count (v : Nat) : ∀ (T : List Nat) (k a : Nat),
    ((T.zipIdx k).filter (fun x => decide (x.2 < a ∧ x.1 ≤ v))).length =
      ((T.take (a - k)).filter (fun c => decide (c ≤ v))).length := by
  intro T
  induction T with
  | nil => intro k a; simp
  | cons c T ih =>
    intro k a
    rw [List.zipIdx_cons, List.filter_cons]
    by_cases hk : k < a
    · have e : a - k = (a - (k + 1)) + 1 := by omega
      rw [e, List.take_succ_cons, List.filter_cons]
      by_cases hc : c ≤ v
      · simp [hk, hc]
        simpa using ih (k + 1) a
      · simp [hk, hc]
        simpa using ih (k + 1) a
    · have h0 : a - k = 0 := by omega
      have := ih (k + 1) a
      have h1 : a - (k + 1) = 0 := by omega
      rw [h1] at this
      simp [hk, h0] at this ⊢
      exact this

private theorem zipIdx_nodup (T : List Nat) : T.zipIdx.Nodup := by
  have := sortedIdx_zipIdx T
  unfold SortedIdx at this
  exact this.imp (fun {a b} h e => by subst e; omega)

private theorem pos_closed (T : List Nat) (D R : List (Nat × Nat)) (cur : List (Nat × Nat))
    (it : Nat × Nat) (hcur : cur.Perm (basicItems T ++ D))
    (hperm : (basicItems T ++ D ++ it :: R).Perm T.zipIdx)
    (hplan : PlanOk (D ++ it :: R)) (hit : 128 ≤ it.1) :
    insertionPosition cur it = ((T.take it.2).filter (fun c => decide (c ≤ it.1))).length := by
  have hnodup : (basicItems T ++ D ++ it :: R).Nodup := hperm.nodup_iff.mpr (zipIdx_nodup T)
  have hnodup' : (basicItems T ++ D).Nodup := hnodup.sublist (List.sublist_append_left _ _)
  have hnodupI : (T.zipIdx.filter (fun x => decide (x.1 < it.1 ∨ (x.1 = it.1 ∧ x.2 < it.2)))).Nodup :=
    (zipIdx_nodup T).sublist List.filter_sublist
  obtain ⟨hD_pw, hit_pw, hD_it⟩ := List.pairwise_append.mp hplan
  obtain ⟨hit_R, _⟩ := List.pairwise_cons.mp hit_pw
  have hmemI : ∀ x, x ∈ basicItems T ++ D ++ it :: R ↔ x ∈ T.zipIdx := fun x => hperm.mem_iff
  have hperm2 : (basicItems T ++ D).Perm
      (T.zipIdx.filter (fun x => decide (x.1 < it.1 ∨ (x.1 = it.1 ∧ x.2 < it.2)))) := by
    rw [List.perm_ext_iff_of_nodup hnodup' hnodupI]
    intro x
    rw [List.mem_filter]
    constructor
    · intro hx
      have hxall : x ∈ basicItems T ++ D ++ it :: R := by
        rcases List.mem_append.mp hx with h | h
        · exact List.mem_append_left _ (List.mem_append_left _ h)
        · exact List.mem_append_left _ (List.mem_append_right _ h)
      refine ⟨(hmemI x).mp hxall, ?_⟩
      rcases List.mem_append.mp hx with hx | hx
      · have := (List.mem_filter.mp hx).2
        simp at this ⊢
        omega
      · have := (hD_it x hx it (by simp)).2
        simpa using this
    · rintro ⟨hx, hs⟩
      have hx' := (hmemI x).mpr hx
      simp only [List.mem_append, List.mem_cons] at hx'
      rcases hx' with (hx' | hx') | rfl | hx'
      · exact List.mem_append_left _ hx'
      · exact List.mem_append_right _ hx'
      · simp at hs
      · have := (hit_R x hx').2
        simp at hs
        omega
  unfold insertionPosition
  rw [(hcur.filter _).length_eq, (hperm2.filter _).length_eq, List.filter_filter]
  have hcongr : T.zipIdx.filter (fun x => decide (x.2 < it.2) &&
      (decide (x.1 < it.1 ∨ (x.1 = it.1 ∧ x.2 < it.2)))) =
      T.zipIdx.filter (fun x => decide (x.2 < it.2 ∧ x.1 ≤ it.1)) := by
    apply List.filter_congr
    intro x _
    by_cases h1 : x.2 < it.2 <;> by_cases h2 : x.1 ≤ it.1 <;> simp [h1, h2] <;> omega
  rw [hcongr, zipIdx_count it.1 T 0 it.2]
  simp

private theorem insertions_eq_closed (T : List Nat) :
    ∀ (R D cur : List (Nat × Nat)) (n i bias : Nat),
      cur.Perm (basicItems T ++ D) →
      (basicItems T ++ D ++ R).Perm T.zipIdx → PlanOk (D ++ R) → (∀ x ∈ R, 128 ≤ x.1) →
      encodeInsertions cur n i bias R =
        closedOut T (basicItems T).length ⟨n, i, bias, D.length⟩ R := by
  intro R
  induction R with
  | nil => intros; simp [encodeInsertions, closedOut]
  | cons it R ih =>
    intro D cur n i bias hcur hperm hplan hge
    have hit : 128 ≤ it.1 := hge it (by simp)
    have hpos := pos_closed T D R cur it hcur hperm hplan hit
    have hlen : cur.length = (basicItems T).length + D.length := by
      rw [hcur.length_eq]; simp
    have hcur' : (insertAt cur (insertionPosition cur it) it).Perm
        (basicItems T ++ (D ++ [it])) := by
      refine (insertAt_perm _ _ _).trans ?_
      refine (hcur.cons it).trans ?_
      rw [← List.append_assoc]
      exact (List.perm_append_singleton it _).symm
    have hperm' : (basicItems T ++ (D ++ [it]) ++ R).Perm T.zipIdx := by
      simpa [List.append_assoc] using hperm
    have hplan' : PlanOk ((D ++ [it]) ++ R) := by simpa [List.append_assoc] using hplan
    have ih' := ih (D ++ [it]) (insertAt cur (insertionPosition cur it) it) it.1
      (insertionPosition cur it + 1)
      (adapt ((it.1 - n) * (cur.length + 1) + insertionPosition cur it - i) (cur.length + 1) (i == 0))
      hcur' hperm' hplan' (fun x hx => hge x (by simp [hx]))
    simp only [encodeInsertions, closedOut, closedStep]
    rw [ih', hpos, hlen]
    simp [Nat.add_assoc]

private def phi (m : Nat) (P : List Nat) : Nat := (P.filter (fun c => decide (c ≤ m))).length

private theorem phi_snoc (m x : Nat) (P : List Nat) :
    phi m (P ++ [x]) = phi m P + (if x ≤ m then 1 else 0) := by
  unfold phi
  rw [List.filter_append]
  by_cases h : x ≤ m <;> simp [h]

private def scanItems (m : Nat) (k : Nat) (Q : List Nat) : List (Nat × Nat) :=
  (Q.zipIdx k).filter (fun x => decide (x.1 = m))

private theorem scan_lemma (T : List Nat) (b m : Nat) :
    ∀ (Q P1 : List Nat) (st : Reference.EncoderState) (cst : CState),
      T = P1 ++ Q → st.n = m → st.handled = b + cst.j → st.bias = cst.bias →
      st.delta + cst.i = (m - cst.n) * (b + cst.j + 1) + phi m P1 →
      cst.n ≤ m → (cst.i = 0 ↔ cst.j = 0) →
      (Q.foldl (Reference.encodeCodePoint b) st).n = m ∧
      (Q.foldl (Reference.encodeCodePoint b) st).output =
        st.output ++ closedOut T b cst (scanItems m P1.length Q) ∧
      (Q.foldl (Reference.encodeCodePoint b) st).handled =
        b + (closedEnd T b cst (scanItems m P1.length Q)).j ∧
      (Q.foldl (Reference.encodeCodePoint b) st).bias =
        (closedEnd T b cst (scanItems m P1.length Q)).bias ∧
      (Q.foldl (Reference.encodeCodePoint b) st).delta +
          (closedEnd T b cst (scanItems m P1.length Q)).i =
        (m - (closedEnd T b cst (scanItems m P1.length Q)).n) *
          (b + (closedEnd T b cst (scanItems m P1.length Q)).j + 1) + phi m T ∧
      (closedEnd T b cst (scanItems m P1.length Q)).n ≤ m ∧
      ((closedEnd T b cst (scanItems m P1.length Q)).i = 0 ↔
        (closedEnd T b cst (scanItems m P1.length Q)).j = 0) := by
  intro Q
  induction Q with
  | nil =>
    intro P1 st cst hT h1 h2 h3 h4 h5 h6
    simp only [List.foldl_nil, scanItems, List.zipIdx_nil, List.filter_nil, closedOut, closedEnd,
      List.append_nil]
    have : T = P1 := by simpa using hT
    subst this
    exact ⟨h1, trivial, h2, h3, h4, h5, h6⟩
  | cons x Q ih =>
    intro P1 st cst hT h1 h2 h3 h4 h5 h6
    have hT' : T = (P1 ++ [x]) ++ Q := by simp [hT]
    have hlen : (P1 ++ [x]).length = P1.length + 1 := by simp
    by_cases hlt : x < m
    · have hst1 : Reference.encodeCodePoint b st x = { st with delta := st.delta + 1 } := by
        simp [Reference.encodeCodePoint, h1, hlt]
      have hne : ¬ x = m := by omega
      have hscan : scanItems m P1.length (x :: Q) = scanItems m (P1 ++ [x]).length Q := by
        simp [scanItems, List.zipIdx_cons, hlen, hne]
      have hphi : phi m (P1 ++ [x]) = phi m P1 + 1 := by
        rw [phi_snoc]; simp; omega
      have key := ih (P1 ++ [x]) { st with delta := st.delta + 1 } cst hT' h1 h2 h3
        (by simp only; omega) h5 h6
      rw [List.foldl_cons, hst1, hscan]
      simpa using key
    · by_cases heq : x = m
      · have hTake : T.take P1.length = P1 := by rw [hT]; exact List.take_left
        have hposphi : ((T.take P1.length).filter (fun c => decide (c ≤ m))).length = phi m P1 := by
          rw [hTake]; rfl
        have hdelta : st.delta = (m - cst.n) * (b + cst.j + 1) + phi m P1 - cst.i := by omega
        have hstep : closedStep T b cst (m, P1.length) =
            (encodeIntegerFrom cst.bias base ((m - cst.n) * (b + cst.j + 1) + phi m P1 - cst.i),
              ⟨m, phi m P1 + 1, adapt ((m - cst.n) * (b + cst.j + 1) + phi m P1 - cst.i)
                (b + cst.j + 1) (cst.i == 0), cst.j + 1⟩) := by
          simp [closedStep, hposphi]
        have hst1 : Reference.encodeCodePoint b st x =
            { st with
              delta := 0
              bias := adapt st.delta (st.handled + 1) (st.handled == b)
              handled := st.handled + 1
              output := st.output ++ encodeIntegerFrom st.bias base st.delta } := by
          simp [Reference.encodeCodePoint, h1, heq]
        have hscan : scanItems m P1.length (x :: Q) =
            (m, P1.length) :: scanItems m (P1 ++ [x]).length Q := by
          simp [scanItems, List.zipIdx_cons, heq]
        have hbool : (st.handled == b) = (cst.i == 0) := by
          have e1 : (st.handled == b) = decide (cst.j = 0) := by
            rw [h2]; by_cases hj : cst.j = 0 <;> simp [hj]
          have e2 : (cst.i == 0) = decide (cst.i = 0) := by
            by_cases hi : cst.i = 0 <;> simp [hi]
          rw [e1, e2]
          exact decide_eq_decide.mpr h6.symm
        have hbias : adapt st.delta (st.handled + 1) (st.handled == b) =
            adapt ((m - cst.n) * (b + cst.j + 1) + phi m P1 - cst.i) (b + cst.j + 1) (cst.i == 0) := by
          rw [hdelta, hbool, h2]
        have hphi : phi m (P1 ++ [x]) = phi m P1 + 1 := by
          rw [phi_snoc]; simp; omega
        have key := ih (P1 ++ [x])
          { st with
            delta := 0
            bias := adapt st.delta (st.handled + 1) (st.handled == b)
            handled := st.handled + 1
            output := st.output ++ encodeIntegerFrom st.bias base st.delta }
          (closedStep T b cst (m, P1.length)).2 hT' h1 (by simp [hstep, h2]; omega)
          (by simp [hstep, hbias]) (by simp [hstep, hphi]) (by simp [hstep]) (by simp [hstep])
        rw [List.foldl_cons, hst1, hscan]
        simp only [closedOut, closedEnd]
        rw [hstep] at key ⊢
        simp only at key ⊢
        simp only [h3, hdelta] at key ⊢
        simpa [List.append_assoc] using key
      · have hgt : m < x := by omega
        have hst1 : Reference.encodeCodePoint b st x = st := by
          simp [Reference.encodeCodePoint, h1, hlt, heq]
        have hscan : scanItems m P1.length (x :: Q) = scanItems m (P1 ++ [x]).length Q := by
          simp [scanItems, List.zipIdx_cons, heq]
        have hphi : phi m (P1 ++ [x]) = phi m P1 := by
          rw [phi_snoc]; simp; omega
        have key := ih (P1 ++ [x]) st cst hT' h1 h2 h3 (by rw [hphi]; exact h4) h5 h6
        rw [List.foldl_cons, hst1, hscan]
        exact key

private theorem foldl_min_spec : ∀ (l : List Nat) (init : Nat),
    l.foldl min init ≤ init ∧ (∀ x ∈ l, l.foldl min init ≤ x) ∧
      (l.foldl min init = init ∨ l.foldl min init ∈ l) := by
  intro l
  induction l with
  | nil => intro init; simp
  | cons y l ih =>
    intro init
    obtain ⟨h1, h2, h3⟩ := ih (min init y)
    simp only [List.foldl_cons]
    refine ⟨by omega, fun x hx => ?_, ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · exact h2 x hx
    · rcases h3 with h | h
      · by_cases hy : init ≤ y
        · left; omega
        · right; simp; omega
      · right; simp [h]

private theorem closedEnd_j (T : List Nat) (b : Nat) : ∀ (G : List (Nat × Nat)) (st : CState),
    (closedEnd T b st G).j = st.j + G.length := by
  intro G
  induction G with
  | nil => intro st; simp [closedEnd]
  | cons it G ih =>
    intro st
    simp only [closedEnd, ih, List.length_cons, closedStep]
    omega

private theorem closedEnd_n (T : List Nat) (b m : Nat) : ∀ (G : List (Nat × Nat)) (st : CState),
    G ≠ [] → (∀ x ∈ G, x.1 = m) → (closedEnd T b st G).n = m := by
  intro G
  induction G with
  | nil => intro st h; exact absurd rfl h
  | cons it G ih =>
    intro st _ hm
    cases G with
    | nil => simp [closedEnd, closedStep, hm it (by simp)]
    | cons it2 G =>
      simp only [closedEnd]
      exact ih _ (by simp) (fun x hx => hm x (by simp [hx]))

private theorem scanItems_length (m : Nat) : ∀ (Q : List Nat) (k : Nat),
    (scanItems m k Q).length = (Q.filter (fun c => decide (c = m))).length := by
  intro Q
  induction Q with
  | nil => intro k; simp [scanItems]
  | cons c Q ih =>
    intro k
    have := ih (k + 1)
    unfold scanItems at this ⊢
    rw [List.zipIdx_cons, List.filter_cons, List.filter_cons]
    by_cases h : c = m <;> simp [h, this]

private theorem count_split (T : List Nat) (N m : Nat) (hNm : N ≤ m)
    (hmin : ∀ c ∈ T, N ≤ c → m ≤ c) :
    (T.filter (fun c => decide (c < N))).length + (T.filter (fun c => decide (c = m))).length =
      (T.filter (fun c => decide (c < m + 1))).length := by
  induction T with
  | nil => simp
  | cons c T ih =>
    have ih' := ih (fun x hx hN => hmin x (by simp [hx]) hN)
    have hc := hmin c (by simp)
    simp only [List.filter_cons]
    by_cases h1 : c < N
    · have h2 : ¬ c = m := by omega
      have h3 : c < m + 1 := by omega
      simp [h1, h2, h3]
      omega
    · have hmc := hc (by omega)
      by_cases h2 : c = m
      · have h3 : c < m + 1 := by omega
        have hmN : ¬ m < N := by omega
        simp [h2, hmN]
        omega
      · have h3 : ¬ c < m + 1 := by omega
        simp [h1, h2, h3]
        omega

private theorem phi_eq_lt (m : Nat) (T : List Nat) :
    phi m T = (T.filter (fun c => decide (c < m + 1))).length := by
  unfold phi
  have h : ∀ x : Nat, decide (x ≤ m) = decide (x < m + 1) := fun x => by
    simp [Nat.lt_succ_iff]
  simp only [h]

private def BInv (T : List Nat) (b : Nat) (st : Reference.EncoderState) (cst : CState)
    (Dl : List (Nat × Nat)) : Prop :=
  st.handled = b + cst.j ∧ st.bias = cst.bias ∧ (cst.i = 0 ↔ cst.j = 0) ∧ cst.n ≤ st.n ∧
  st.delta + cst.i = (st.n - cst.n) * (b + cst.j + 1) ∧
  b + cst.j = (T.filter (fun c => decide (c < st.n))).length ∧ 128 ≤ st.n ∧
  (∀ x, x ∈ Dl ↔ (x ∈ T.zipIdx ∧ 128 ≤ x.1 ∧ x.1 < st.n)) ∧
  Dl.Pairwise (fun a c => a.2 ≠ c.2 ∧ (a.1 < c.1 ∨ (a.1 = c.1 ∧ a.2 < c.2)))

private theorem inj_of_nodup_snd : ∀ (l : List (Nat × Nat)), (l.map Prod.snd).Nodup →
    ∀ x ∈ l, ∀ y ∈ l, x.2 = y.2 → x = y := by
  intro l
  induction l with
  | nil => intro _ x hx; simp at hx
  | cons a l ih =>
    intro hnd x hx y hy e
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnotin, hnd'⟩ := hnd
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · exact absurd (e ▸ List.mem_map_of_mem (f := Prod.snd) hy') hnotin
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd (e ▸ List.mem_map_of_mem (f := Prod.snd) hx') hnotin
      · exact ih hnd' x hx' y hy' e

private theorem zipIdx_inj (T : List Nat) : ∀ x ∈ T.zipIdx, ∀ y ∈ T.zipIdx, x.2 = y.2 → x = y := by
  have h : (T.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]; exact List.nodup_range'
  exact inj_of_nodup_snd _ h

private theorem exists_ge (T : List Nat) (b : Nat) (n j : Nat)
    (h : b + j = (T.filter (fun c => decide (c < n))).length)
    (hlt : b + j < T.length) : ∃ c ∈ T, n ≤ c := by
  by_cases hall : ∀ c ∈ T, c < n
  · have : T.filter (fun c => decide (c < n)) = T := by
      rw [List.filter_eq_self]; intro c hc; simpa using hall c hc
    rw [this] at h; omega
  · apply Classical.byContradiction
    intro hno
    apply hall
    intro c hc
    exact Nat.lt_of_not_le (fun hle => hno ⟨c, hc, hle⟩)

private theorem pass_lemma (T : List Nat) (b : Nat) (hT : ∀ x ∈ T, x < 0x110000)
    (st : Reference.EncoderState) (cst : CState) (Dl : List (Nat × Nat))
    (hinv : BInv T b st cst Dl) (hlt : st.handled < T.length) :
    ∃ G, G ≠ [] ∧ BInv T b (Reference.encodeStep b T st) (closedEnd T b cst G) (Dl ++ G) ∧
      (Reference.encodeStep b T st).output = st.output ++ closedOut T b cst G ∧
      st.handled < (Reference.encodeStep b T st).handled := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hinv
  obtain ⟨c0, hc0T, hc0⟩ := exists_ge T b st.n cst.j h6 (by omega)
  obtain ⟨hmle, hmall, hmmem⟩ := foldl_min_spec (T.filter (fun x => decide (x ≥ st.n))) 0x110000
  generalize hm : (T.filter (fun x => decide (x ≥ st.n))).foldl min 0x110000 = m at hmle hmall hmmem
  have hc0mem : c0 ∈ T.filter (fun x => decide (x ≥ st.n)) :=
    List.mem_filter.mpr ⟨hc0T, by simpa using hc0⟩
  have hmlt : m ≠ 0x110000 := by
    have := hmall c0 hc0mem
    have := hT c0 hc0T
    omega
  have hmmem' : m ∈ T.filter (fun x => decide (x ≥ st.n)) := hmmem.resolve_left hmlt
  have hmT : m ∈ T := (List.mem_filter.mp hmmem').1
  have hNm : st.n ≤ m := by simpa using (List.mem_filter.mp hmmem').2
  have hmin : ∀ c ∈ T, st.n ≤ c → m ≤ c := fun c hc hn =>
    hmall c (List.mem_filter.mpr ⟨hc, by simpa using hn⟩)
  have hstep : Reference.encodeStep b T st =
      { (T.foldl (Reference.encodeCodePoint b)
          { st with delta := st.delta + (m - st.n) * (st.handled + 1), n := m }) with
        delta := (T.foldl (Reference.encodeCodePoint b)
          { st with delta := st.delta + (m - st.n) * (st.handled + 1), n := m }).delta + 1,
        n := (T.foldl (Reference.encodeCodePoint b)
          { st with delta := st.delta + (m - st.n) * (st.handled + 1), n := m }).n + 1 } := by
    unfold Reference.encodeStep
    simp only [hm]
  have hphi0 : phi m [] = 0 := by simp [phi]
  have hscan := scan_lemma T b m T []
    { st with delta := st.delta + (m - st.n) * (st.handled + 1), n := m } cst (by simp) rfl
    (by simpa using h1) (by simpa using h2)
    (by
      simp only [hphi0]
      have e : m - cst.n = (st.n - cst.n) + (m - st.n) := by omega
      rw [e, Nat.add_mul, ← h1]
      rw [← h1] at h5
      omega)
    (by omega) h3
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hscan
  simp only [List.length_nil] at s2 s3 s4 s5 s6 s7
  generalize hr : T.foldl (Reference.encodeCodePoint b)
    { st with delta := st.delta + (m - st.n) * (st.handled + 1), n := m } = r at hstep s1 s2 s3 s4 s5 s6 s7
  have hGmem : ∀ x, x ∈ scanItems m 0 T ↔ x ∈ T.zipIdx ∧ x.1 = m := by
    intro x; unfold scanItems; rw [List.mem_filter]; simp
  have hGlen : (scanItems m 0 T).length = (T.filter (fun c => decide (c = m))).length :=
    scanItems_length m T 0
  have hGne : scanItems m 0 T ≠ [] := by
    intro h
    have : (T.filter (fun c => decide (c = m))) ≠ [] :=
      List.ne_nil_of_mem (List.mem_filter.mpr ⟨hmT, by simp⟩)
    rw [h] at hGlen
    exact this (List.length_eq_zero_iff.mp hGlen.symm)
  have hGval : ∀ x ∈ scanItems m 0 T, x.1 = m := fun x hx => ((hGmem x).mp hx).2
  have hn' := closedEnd_n T b m (scanItems m 0 T) cst hGne hGval
  have hj' := closedEnd_j T b (scanItems m 0 T) cst
  have hcount := count_split T st.n m hNm hmin
  have hphi := phi_eq_lt m T
  have hbj' : b + (closedEnd T b cst (scanItems m 0 T)).j = phi m T := by
    rw [hj', hphi, ← hcount, ← h6, hGlen]; omega
  have hGpos : 0 < (scanItems m 0 T).length := List.length_pos_iff.mpr hGne
  have hmemDl : ∀ x, x ∈ Dl ++ scanItems m 0 T ↔ (x ∈ T.zipIdx ∧ 128 ≤ x.1 ∧ x.1 < m + 1) := by
    intro x
    constructor
    · intro hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨a, b', c⟩ := (h8 x).mp hx
        exact ⟨a, b', by omega⟩
      · obtain ⟨a, b'⟩ := (hGmem x).mp hx
        exact ⟨a, by omega, by omega⟩
    · rintro ⟨hxI, hge, hlt'⟩
      by_cases hlt2 : x.1 < st.n
      · exact List.mem_append_left _ ((h8 x).mpr ⟨hxI, hge, hlt2⟩)
      · have hxT : x.1 ∈ T := by
          have := List.mem_map_of_mem (f := Prod.fst) hxI
          rwa [List.zipIdx_map_fst] at this
        have := hmin x.1 hxT (by omega)
        exact List.mem_append_right _ ((hGmem x).mpr ⟨hxI, by omega⟩)
  have hpwG : (scanItems m 0 T).Pairwise
      (fun a c => a.2 ≠ c.2 ∧ (a.1 < c.1 ∨ (a.1 = c.1 ∧ a.2 < c.2))) := by
    have h0 : (scanItems m 0 T).Pairwise (fun a c => a.2 < c.2) := by
      have := sortedIdx_zipIdx T
      unfold SortedIdx at this
      exact this.sublist List.filter_sublist
    refine h0.imp_of_mem ?_
    intro a c ha hc hac
    have := hGval a ha
    have := hGval c hc
    exact ⟨by omega, Or.inr ⟨by omega, hac⟩⟩
  have hpw : (Dl ++ scanItems m 0 T).Pairwise
      (fun a c => a.2 ≠ c.2 ∧ (a.1 < c.1 ∨ (a.1 = c.1 ∧ a.2 < c.2))) := by
    refine List.pairwise_append.mpr ⟨h9, hpwG, ?_⟩
    intro a ha g hg
    obtain ⟨haI, _, halt⟩ := (h8 a).mp ha
    obtain ⟨hgI, hgm⟩ := (hGmem g).mp hg
    refine ⟨fun e => ?_, Or.inl (by omega)⟩
    have := zipIdx_inj T a haI g hgI e
    rw [this] at halt
    omega
  refine ⟨scanItems m 0 T, hGne, ?_, ?_, ?_⟩
  · rw [hstep]
    dsimp only
    refine ⟨s3, s4, s7, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only
      omega
    · dsimp only
      rw [hn'] at s5
      simp only [Nat.sub_self, Nat.zero_mul, Nat.zero_add] at s5
      rw [s1, hn']
      have : m + 1 - m = 1 := by omega
      rw [this, Nat.one_mul]
      omega
    · dsimp only
      rw [s1, hbj', hphi]
    · dsimp only
      omega
    · dsimp only
      rw [s1]; exact hmemDl
    · exact hpw
  · rw [hstep]; simpa using s2
  · rw [hstep]
    dsimp only
    omega

private theorem loop_lemma (T : List Nat) (b : Nat) (hT : ∀ x ∈ T, x < 0x110000) :
    ∀ (fuel : Nat) (st : Reference.EncoderState) (cst : CState) (Dl : List (Nat × Nat)),
      BInv T b st cst Dl → T.length - st.handled ≤ fuel →
      ∃ G : List (Nat × Nat),
        BInv T b (Reference.encodeLoop b T fuel st) (closedEnd T b cst G) (Dl ++ G) ∧
        (Reference.encodeLoop b T fuel st).output = st.output ++ closedOut T b cst G ∧
        T.length ≤ (Reference.encodeLoop b T fuel st).handled := by
  intro fuel
  induction fuel with
  | zero =>
    intro st cst Dl hinv hfuel
    refine ⟨[], ?_, ?_, ?_⟩
    · simpa [Reference.encodeLoop, closedEnd] using hinv
    · simp [Reference.encodeLoop, closedOut]
    · simp [Reference.encodeLoop]; omega
  | succ fuel ih =>
    intro st cst Dl hinv hfuel
    by_cases hlt : st.handled < T.length
    · obtain ⟨G, hGne, hinv', hout, hmono⟩ := pass_lemma T b hT st cst Dl hinv hlt
      have hrec := ih (Reference.encodeStep b T st) (closedEnd T b cst G) (Dl ++ G) hinv'
        (by omega)
      obtain ⟨G', hinv'', hout', hdone⟩ := hrec
      refine ⟨G ++ G', ?_, ?_, ?_⟩
      · rw [closedEnd_append, ← List.append_assoc]
        have e : Reference.encodeLoop b T (fuel + 1) st =
            Reference.encodeLoop b T fuel (Reference.encodeStep b T st) := by
          simp [Reference.encodeLoop, hlt]
        rw [e]
        exact hinv''
      · have e : Reference.encodeLoop b T (fuel + 1) st =
            Reference.encodeLoop b T fuel (Reference.encodeStep b T st) := by
          simp [Reference.encodeLoop, hlt]
        rw [e, hout', hout, closedOut_append, List.append_assoc]
      · have e : Reference.encodeLoop b T (fuel + 1) st =
            Reference.encodeLoop b T fuel (Reference.encodeStep b T st) := by
          simp [Reference.encodeLoop, hlt]
        rw [e]; exact hdone
    · refine ⟨[], ?_, ?_, ?_⟩
      · have e : Reference.encodeLoop b T (fuel + 1) st = st := by simp [Reference.encodeLoop, hlt]
        rw [e]; simpa [closedEnd] using hinv
      · have e : Reference.encodeLoop b T (fuel + 1) st = st := by simp [Reference.encodeLoop, hlt]
        rw [e]; simp [closedOut]
      · have e : Reference.encodeLoop b T (fuel + 1) st = st := by simp [Reference.encodeLoop, hlt]
        rw [e]; omega

private theorem zipIdx_filter_map_fst (p : Nat → Bool) : ∀ (T : List Nat) (k : Nat),
    ((T.zipIdx k).filter (fun x => p x.1)).map Prod.fst = T.filter p := by
  intro T
  induction T with
  | nil => intro k; simp
  | cons c T ih =>
    intro k
    rw [List.zipIdx_cons, List.filter_cons, List.filter_cons]
    by_cases h : p c = true <;> simp [h, ih]

private theorem basicItems_map_fst (T : List Nat) :
    (basicItems T).map Prod.fst = T.filter (fun c => decide (c < 128)) := by
  unfold basicItems
  exact zipIdx_filter_map_fst (fun c => decide (c < 128)) T 0

private theorem basic_chars (s : String) :
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

private theorem emitted_eq_plan (T : List Nat) (G : List (Nat × Nat)) (n : Nat)
    (hmem : ∀ x, x ∈ G ↔ (x ∈ T.zipIdx ∧ 128 ≤ x.1 ∧ x.1 < n))
    (hpw : G.Pairwise (fun a c => a.2 ≠ c.2 ∧ (a.1 < c.1 ∨ (a.1 = c.1 ∧ a.2 < c.2))))
    (hall : ∀ c ∈ T, c < n) : G = planOf T := by
  have hok := planOf_ok T
  have hplanmem : ∀ x, x ∈ planOf T ↔ (x ∈ T.zipIdx ∧ 128 ≤ x.1) := by
    intro x
    unfold planOf
    rw [(List.mergeSort_perm _ _).mem_iff, List.mem_filter]
    simp
  have hGmem : ∀ x, x ∈ G ↔ (x ∈ T.zipIdx ∧ 128 ≤ x.1) := by
    intro x
    rw [hmem x]
    constructor
    · rintro ⟨a, b, _⟩; exact ⟨a, b⟩
    · rintro ⟨a, b⟩
      have hxT : x.1 ∈ T := by
        have := List.mem_map_of_mem (f := Prod.fst) a
        rwa [List.zipIdx_map_fst] at this
      exact ⟨a, b, hall x.1 hxT⟩
  have hndG : G.Nodup := hpw.imp (fun {a c} h e => h.1 (by rw [e]))
  have hndP : (planOf T).Nodup := by
    unfold PlanOk at hok
    exact hok.imp (fun {a c} h e => h.1 (by rw [e]))
  have hperm : G.Perm (planOf T) := by
    rw [List.perm_ext_iff_of_nodup hndG hndP]
    intro x
    rw [hGmem, hplanmem]
  exact List.Perm.eq_of_pairwise (le := fun (a c : Nat × Nat) =>
      a.2 ≠ c.2 ∧ (a.1 < c.1 ∨ (a.1 = c.1 ∧ a.2 < c.2)))
    (fun a c _ _ h1 h2 => by omega) hpw hok hperm

theorem reference_encode_eq (s : String) : Reference.encode s = encode s := by
  have hT : ∀ x ∈ s.toList.map Char.toNat, x < 0x110000 := by
    intro x hx
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
    have h : Nat.isValidChar c.toNat := c.valid
    rcases h with h | ⟨_, h⟩ <;> omega
  have hbc := basic_chars s
  have hbl : (s.toList.filter (fun c => decide (c.toNat < 128))).length =
      (basicItems (s.toList.map Char.toNat)).length := by
    have := congrArg List.length hbc
    simpa using this.symm
  have hb128 : (basicItems (s.toList.map Char.toNat)).length =
      ((s.toList.map Char.toNat).filter (fun c => decide (c < 128))).length := by
    have := congrArg List.length (basicItems_map_fst (s.toList.map Char.toNat))
    simpa using this
  unfold Reference.encode encode
  dsimp only
  rw [hbl, ← hbc]
  generalize hTdef : s.toList.map Char.toNat = T at hT hb128 ⊢
  generalize hbdef : (basicItems T).length = b at hb128 ⊢
  have hemp : ((basicItems T).map (fun x => Char.ofNat x.1)).isEmpty = (basicItems T).isEmpty := by
    simp
  rw [hemp]
  generalize hP : (if (basicItems T).isEmpty = true then []
    else (basicItems T).map (fun x => Char.ofNat x.fst) ++ [delimiter]) = P
  congr 1
  have hinit : BInv T b { n := initialN, delta := 0, bias := initialBias, handled := b, output := P }
      ⟨initialN, 0, initialBias, 0⟩ [] := by
    refine ⟨rfl, rfl, Iff.rfl, Nat.le_refl _, ?_, ?_, ?_, ?_, List.Pairwise.nil⟩
    · simp
    · simp only [Nat.add_zero]
      rw [hb128]
      unfold initialN
      rfl
    · show 128 ≤ initialN
      unfold initialN; decide
    · intro x
      constructor
      · intro hx; simp at hx
      · rintro ⟨_, h1, h2⟩
        have h2' : x.1 < initialN := h2
        unfold initialN at h2'
        omega
  obtain ⟨G, hinvF, houtF, hdone⟩ := loop_lemma T b hT (T.length + 1)
    { n := initialN, delta := 0, bias := initialBias, handled := b, output := P }
    ⟨initialN, 0, initialBias, 0⟩ [] hinit (by omega)
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := hinvF
  generalize hF : Reference.encodeLoop b T (T.length + 1)
    { n := initialN, delta := 0, bias := initialBias, handled := b, output := P } = F at *
  have hall : ∀ c ∈ T, c < F.n := by
    have hle : (T.filter (fun c => decide (c < F.n))).length ≤ T.length := List.length_filter_le _ _
    have heq : (T.filter (fun c => decide (c < F.n))).length = T.length := by omega
    intro c hc
    have := (List.length_filter_eq_length_iff.mp heq) c hc
    simpa using this
  have hG : G = planOf T := emitted_eq_plan T G F.n (by simpa using f8) f9 hall
  have hplan := planOf_ok T
  have hperm := basic_plan_perm T
  have hge : ∀ x ∈ planOf T, 128 ≤ x.1 := by
    intro x hx
    unfold planOf at hx
    have := (List.mergeSort_perm _ _).mem_iff.mp hx
    simpa using (List.mem_filter.mp this).2
  have hins := insertions_eq_closed T (planOf T) [] (basicItems T) initialN 0 initialBias
    (by simp) (by simpa using hperm) (by simpa using hplan) hge
  rw [houtF, hG, hins, hbdef]
  simp

end Urllib.Punycode
