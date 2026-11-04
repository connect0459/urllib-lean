import Urllib.Host.Ipv6

namespace Urllib.Host.Ipv6

private def digitsValue (acc : Nat) (ds : List Char) : Nat :=
  ds.foldl (fun a c => a * 16 + ((Ipv4.digitValue? 16 c).getD 0)) acc

private theorem digitValue_hexChar : ∀ d, d < 16 → Ipv4.digitValue? 16 (hexChar d) = some d := by
  decide

private theorem hexChar_ne_colon : ∀ d, d < 16 → hexChar d ≠ ':' := by
  decide

private theorem hexDigits_valid : ∀ p, ∀ c ∈ hexDigits p, ∃ d, d < 16 ∧ c = hexChar d := by
  intro p
  induction p using Nat.strongRecOn with
  | _ p ih =>
    rw [hexDigits]
    split
    · intro c hc
      simp only [List.mem_singleton] at hc
      exact ⟨p, by omega, hc⟩
    · intro c hc
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | hc
      · exact ih (p / 16) (by omega) c hc
      · exact ⟨p % 16, by omega, hc⟩

private theorem hexDigits_ne_colon (p : Nat) : ∀ c ∈ hexDigits p, c ≠ ':' := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := hexDigits_valid p c hc
  exact hexChar_ne_colon d hd

private theorem hexDigits_isSome (p : Nat) : ∀ c ∈ hexDigits p, (Ipv4.digitValue? 16 c).isSome := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := hexDigits_valid p c hc
  rw [digitValue_hexChar d hd]
  rfl

private theorem hexDigits_ne_nil (p : Nat) : hexDigits p ≠ [] := by
  rw [hexDigits]
  split <;> simp

private theorem hexDigits_value : ∀ p, digitsValue 0 (hexDigits p) = p := by
  intro p
  induction p using Nat.strongRecOn with
  | _ p ih =>
    rw [hexDigits]
    split
    · simp [digitsValue, digitValue_hexChar p (by omega)]
    · have h := ih (p / 16) (by omega)
      simp only [digitsValue, List.foldl_append, List.foldl_cons, List.foldl_nil] at h ⊢
      rw [h, digitValue_hexChar (p % 16) (by omega)]
      simp
      omega

private theorem hexDigits_length : ∀ n p, p < 16 ^ (n + 1) → (hexDigits p).length ≤ n + 1 := by
  intro n
  induction n with
  | zero =>
    intro p hp
    rw [hexDigits]
    split
    · simp
    · simp at hp; omega
  | succ n ih =>
    intro p hp
    rw [hexDigits]
    split
    · simp
    · have h := ih (p / 16) (by rw [Nat.pow_succ] at hp; omega)
      simp only [List.length_append, List.length_singleton]
      omega

private theorem digitValue_colon : Ipv4.digitValue? 16 ':' = none := by decide

private theorem readHex_digits : ∀ (ds : List Char) budget acc len (rest : List Char),
    (∀ c ∈ ds, (Ipv4.digitValue? 16 c).isSome) → ds.length ≤ budget →
    (rest = [] ∨ ∃ r, rest = ':' :: r) →
    readHex budget acc len (ds ++ rest) = (digitsValue acc ds, len + ds.length, rest) := by
  intro ds
  induction ds with
  | nil =>
    intro budget acc len rest _ _ hrest
    cases budget with
    | zero => simp [readHex, digitsValue]
    | succ b =>
      rcases hrest with rfl | ⟨r, rfl⟩
      · simp [readHex, digitsValue]
      · simp [readHex, digitValue_colon, digitsValue]
  | cons c ds ih =>
    intro budget acc len rest hvalid hlen hrest
    cases budget with
    | zero => simp at hlen
    | succ b =>
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hvalid c (by simp))
      have hvalid' : ∀ x ∈ ds, (Ipv4.digitValue? 16 x).isSome := fun x hx => hvalid x (by simp [hx])
      have := ih b (acc * 16 + d) (len + 1) rest hvalid' (by simp at hlen; omega) hrest
      simp only [List.cons_append, readHex, hd]
      simp only [digitsValue, List.foldl_cons, hd, Option.getD_some] at this ⊢
      rw [this]
      simp [Nat.add_assoc, Nat.add_comm 1]

private theorem parseLoop_hex_end (fuel : Nat) (st : ParseState) (c : Char) (rest : List Char)
    (value len : Nat) (hne : st.pieceIndex ≠ 8) (hc : c ≠ ':')
    (hr : readHex 4 0 0 (c :: rest) = (value, len, [])) :
    parseLoop (fuel + 1) st (c :: rest) = .ok (st.setPiece value) := by
  rw [parseLoop]
  simp only [hne, hc, ite_false]
  rw [hr]

private theorem parseLoop_hex_colon (fuel : Nat) (st : ParseState) (c : Char) (rest afterColon : List Char)
    (value len : Nat) (hne : st.pieceIndex ≠ 8) (hc : c ≠ ':') (hnonempty : afterColon ≠ [])
    (hr : readHex 4 0 0 (c :: rest) = (value, len, ':' :: afterColon)) :
    parseLoop (fuel + 1) st (c :: rest) = parseLoop fuel (st.setPiece value) afterColon := by
  rw [parseLoop]
  simp only [hne, hc, ite_false]
  rw [hr]
  simp [hnonempty]

private theorem parseLoop_colon (fuel : Nat) (st : ParseState) (rest : List Char)
    (hne : st.pieceIndex ≠ 8) (hcompress : st.compress = none) :
    parseLoop (fuel + 1) st (':' :: rest) =
      parseLoop fuel { st with pieceIndex := st.pieceIndex + 1, compress := some (st.pieceIndex + 1) } rest := by
  rw [parseLoop]
  simp [hne, hcompress]

private def writePieces (l : List Nat) (i : Nat) : List Nat → List Nat
  | [] => l
  | p :: ps => writePieces (l.set i p) (i + 1) ps

private def showPieces : List Nat → List Char
  | [] => []
  | [p] => hexDigits p
  | p :: q :: ps => hexDigits p ++ ':' :: showPieces (q :: ps)

private def headChars : List Nat → List Char
  | [] => []
  | p :: ps => hexDigits p ++ ':' :: headChars ps

private theorem readHex_piece (p : Nat) (hp : p < 65536) (rest : List Char)
    (hrest : rest = [] ∨ ∃ r, rest = ':' :: r) :
    readHex 4 0 0 (hexDigits p ++ rest) = (p, (hexDigits p).length, rest) := by
  have hlen : (hexDigits p).length ≤ 4 := hexDigits_length 3 p (by simpa using hp)
  have := readHex_digits (hexDigits p) 4 0 0 rest (hexDigits_isSome p) hlen hrest
  rw [this, hexDigits_value]
  simp

private theorem showPieces_ne_nil : ∀ ps : List Nat, ps ≠ [] → showPieces ps ≠ [] := by
  intro ps hps
  match ps, hps with
  | [p], _ => simpa [showPieces] using hexDigits_ne_nil p
  | p :: q :: ps, _ => simp [showPieces]

private theorem parseLoop_tail : ∀ (ps : List Nat) (st : ParseState) (fuel : Nat),
    ps ≠ [] → (∀ p ∈ ps, p < 65536) → st.pieceIndex + ps.length ≤ 8 →
    (showPieces ps).length < fuel →
    parseLoop fuel st (showPieces ps) =
      .ok { st with
        pieces := writePieces st.pieces st.pieceIndex ps
        pieceIndex := st.pieceIndex + ps.length } := by
  intro ps
  induction ps with
  | nil => intro _ _ h; exact absurd rfl h
  | cons p ps' ih =>
    intro st fuel _ hp hbound hfuel
    have hp0 : p < 65536 := hp p (by simp)
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (hexDigits_ne_nil p)
    have hc : c ≠ ':' := hexDigits_ne_colon p c (by rw [hcs]; simp)
    have hne : st.pieceIndex ≠ 8 := by simp at hbound; omega
    cases ps' with
    | nil =>
      simp only [showPieces] at hfuel ⊢
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by rw [hcs] at hfuel; simp at hfuel; omega⟩
      rw [hcs]
      have hr : readHex 4 0 0 (c :: cs) = (p, (hexDigits p).length, []) := by
        have := readHex_piece p hp0 [] (Or.inl rfl)
        rw [hcs] at this ⊢
        simpa using this
      rw [parseLoop_hex_end f st c cs p _ hne hc hr]
      simp [writePieces, ParseState.setPiece]
    | cons q ps'' =>
      simp only [showPieces] at hfuel ⊢
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by
        have := hexDigits_ne_nil p
        have : 0 < (hexDigits p).length := List.length_pos_iff.mpr this
        simp only [List.length_append, List.length_cons] at hfuel; omega⟩
      have hrest : ∃ r, (':' :: showPieces (q :: ps'')) = ':' :: r := ⟨_, rfl⟩
      have hr0 := readHex_piece p hp0 (':' :: showPieces (q :: ps'')) (Or.inr hrest)
      rw [hcs] at hr0
      have hrr : readHex 4 0 0 (c :: (cs ++ ':' :: showPieces (q :: ps''))) =
          (p, cs.length + 1, ':' :: showPieces (q :: ps'')) := by simpa using hr0
      have hnonempty : showPieces (q :: ps'') ≠ [] := showPieces_ne_nil _ (by simp)
      rw [hcs]
      have hcons : c :: cs ++ ':' :: showPieces (q :: ps'') =
          c :: (cs ++ ':' :: showPieces (q :: ps'')) := by simp
      rw [hcons, parseLoop_hex_colon f st c _ (showPieces (q :: ps'')) p _ hne hc hnonempty hrr]
      have ih' := ih (st.setPiece p) f (by simp) (fun x hx => hp x (by simp [hx]))
        (by simp [ParseState.setPiece] at hbound ⊢; omega)
        (by
          have : 0 < (hexDigits p).length := List.length_pos_iff.mpr (hexDigits_ne_nil p)
          rw [hcs] at this hfuel
          simp only [List.length_append, List.length_cons] at hfuel
          omega)
      rw [ih']
      simp [writePieces, ParseState.setPiece]
      omega


private theorem parseLoop_head : ∀ (ps : List Nat) (st : ParseState) (fuel : Nat) (rest : List Char),
    (∀ p ∈ ps, p < 65536) → st.pieceIndex + ps.length < 8 →
    (headChars ps ++ ':' :: rest).length < fuel →
    parseLoop fuel st (headChars ps ++ ':' :: rest) =
      parseLoop (fuel - ps.length)
        { st with
          pieces := writePieces st.pieces st.pieceIndex ps
          pieceIndex := st.pieceIndex + ps.length } (':' :: rest) := by
  intro ps
  induction ps with
  | nil => intro st fuel rest _ _ _; simp [headChars, writePieces]
  | cons p ps' ih =>
    intro st fuel rest hp hbound hfuel
    have hp0 : p < 65536 := hp p (by simp)
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (hexDigits_ne_nil p)
    have hc : c ≠ ':' := hexDigits_ne_colon p c (by rw [hcs]; simp)
    have hne : st.pieceIndex ≠ 8 := by simp at hbound; omega
    have hlenpos : 0 < (hexDigits p).length := List.length_pos_iff.mpr (hexDigits_ne_nil p)
    simp only [headChars, List.length_append, List.length_cons] at hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hrest : ∃ r, (':' :: (headChars ps' ++ ':' :: rest)) = ':' :: r := ⟨_, rfl⟩
    have hr0 := readHex_piece p hp0 (':' :: (headChars ps' ++ ':' :: rest)) (Or.inr hrest)
    rw [hcs] at hr0 hlenpos
    have hrr : readHex 4 0 0 (c :: (cs ++ ':' :: (headChars ps' ++ ':' :: rest))) =
        (p, cs.length + 1, ':' :: (headChars ps' ++ ':' :: rest)) := by simpa using hr0
    have hnonempty : headChars ps' ++ ':' :: rest ≠ [] := by simp
    rw [show headChars (p :: ps') ++ ':' :: rest =
        hexDigits p ++ ':' :: (headChars ps' ++ ':' :: rest) by simp [headChars], hcs]
    have hcons : c :: cs ++ ':' :: (headChars ps' ++ ':' :: rest) =
        c :: (cs ++ ':' :: (headChars ps' ++ ':' :: rest)) := by simp
    rw [hcons, parseLoop_hex_colon f st c _ (headChars ps' ++ ':' :: rest) p _ hne hc hnonempty hrr]
    have ih' := ih (st.setPiece p) f rest (fun x hx => hp x (by simp [hx]))
      (by simp [ParseState.setPiece] at hbound ⊢; omega)
      (by simp only [List.length_append, List.length_cons] at hfuel ⊢; omega)
    rw [ih']
    have : f + 1 - (ps'.length + 1) = f - ps'.length := by omega
    simp only [List.length_cons, this, writePieces, ParseState.setPiece]
    congr 2
    omega

private theorem writePieces_eq : ∀ (ps l : List Nat) (i : Nat), i + ps.length ≤ l.length →
    writePieces l i ps = l.take i ++ ps ++ l.drop (i + ps.length) := by
  intro ps
  induction ps with
  | nil => intro l i _; simp [writePieces]
  | cons p ps' ih =>
    intro l i h
    simp only [List.length_cons] at h
    have hil : i < l.length := by omega
    have hmin : min i l.length = i := Nat.min_eq_left (by omega)
    rw [writePieces, ih (l.set i p) (i + 1) (by simp; omega)]
    rw [List.set_eq_take_append_cons_drop]
    simp only [hil, ↓reduceIte]
    have h1 : (List.take i l ++ p :: List.drop (i + 1) l).take (i + 1) = List.take i l ++ [p] := by
      rw [List.take_append]
      simp [List.length_take, hmin, List.take_take]
    have h2 : (List.take i l ++ p :: List.drop (i + 1) l).drop (i + 1 + ps'.length) =
        List.drop (i + (ps'.length + 1)) l := by
      rw [List.drop_append]
      have hnil : List.drop (i + 1 + ps'.length) (List.take i l) = [] := by
        apply List.drop_eq_nil_of_le
        simp [List.length_take, hmin]
        omega
      have hsub : i + 1 + ps'.length - i = ps'.length + 1 := by omega
      rw [hnil]
      simp [List.length_take, hmin, hsub, List.drop_drop]
      congr 1
      omega
    rw [h1, h2]
    simp [List.append_assoc]

private theorem expand_writes (head tail : List Nat) (L : Nat) (hL : 1 ≤ L)
    (hsize : head.length + L + tail.length = 8) :
    expandCompression (writePieces (writePieces (List.replicate 8 0) 0 head) (head.length + 1) tail)
      (head.length + 1) tail.length = head ++ List.replicate L 0 ++ tail := by
  have hl1 : writePieces (List.replicate 8 0) 0 head = head ++ List.replicate (8 - head.length) 0 := by
    rw [writePieces_eq _ _ _ (by simp; omega)]
    simp only [List.take_zero, List.nil_append, Nat.zero_add, List.drop_replicate]
  rw [hl1]
  have hlen1 : (head ++ List.replicate (8 - head.length) 0).length = 8 := by simp; omega
  rw [writePieces_eq _ _ _ (by omega)]
  have e1 : (head ++ List.replicate (8 - head.length) 0).take (head.length + 1) = head ++ [0] := by
    rw [List.take_append]
    have : 8 - head.length ≥ 1 := by omega
    obtain ⟨m, hm⟩ : ∃ m, 8 - head.length = m + 1 := ⟨8 - head.length - 1, by omega⟩
    have ht : List.take (head.length + 1) head = head := List.take_of_length_le (by omega)
    simp [hm, List.replicate_succ, ht]
  unfold expandCompression
  have e2 : (List.take (head.length + 1) (head ++ List.replicate (8 - head.length) 0) ++ tail ++
      List.drop (head.length + 1 + tail.length) (head ++ List.replicate (8 - head.length) 0)).take
        (head.length + 1) = head ++ [0] := by
    rw [e1, List.append_assoc, List.take_append_of_le_length (by simp)]
    exact List.take_of_length_le (by simp)
  have e3 : ((List.take (head.length + 1) (head ++ List.replicate (8 - head.length) 0) ++ tail ++
      List.drop (head.length + 1 + tail.length) (head ++ List.replicate (8 - head.length) 0)).drop
        (head.length + 1)).take tail.length = tail := by
    rw [e1, List.append_assoc, List.drop_append_of_le_length (by simp)]
    have hd : List.drop (head.length + 1) (head ++ [0]) = [] :=
      List.drop_eq_nil_of_le (by simp)
    rw [hd, List.nil_append, List.take_append_of_le_length (Nat.le_refl _)]
    exact List.take_of_length_le (Nat.le_refl _)
  rw [e2, e3]
  have hrep : List.replicate (8 - (head.length + 1) - tail.length) 0 = List.replicate (L - 1) 0 := by
    congr 1; omega
  rw [hrep]
  have : head ++ [0] ++ List.replicate (L - 1) 0 ++ tail = head ++ List.replicate L 0 ++ tail := by
    obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
    simp [List.replicate_succ]
  exact this

private theorem parseLoop_tail' (ps : List Nat) (st : ParseState) (fuel : Nat)
    (hp : ∀ p ∈ ps, p < 65536) (hbound : st.pieceIndex + ps.length ≤ 8)
    (hfuel : (showPieces ps).length < fuel) :
    parseLoop fuel st (showPieces ps) =
      .ok { st with
        pieces := writePieces st.pieces st.pieceIndex ps
        pieceIndex := st.pieceIndex + ps.length } := by
  cases ps with
  | nil => cases fuel <;> simp [showPieces, parseLoop, writePieces]
  | cons p ps' => exact parseLoop_tail (p :: ps') st fuel (by simp) hp hbound hfuel

private theorem headChars_length_ge : ∀ ps : List Nat, ps.length ≤ (headChars ps).length := by
  intro ps
  induction ps with
  | nil => simp [headChars]
  | cons p ps ih =>
    have := List.length_pos_iff.mpr (hexDigits_ne_nil p)
    simp only [headChars, List.length_cons, List.length_append]
    omega

private theorem parseChars_not_colon (chars : List Char) (h : ∀ rest, chars ≠ ':' :: rest) :
    parseChars chars = parseLoop (chars.length + 1) {} chars >>= finishParse := by
  cases chars with
  | nil => rfl
  | cons c rest =>
    by_cases hc : c = ':'
    · subst hc
      exact absurd rfl (h rest)
    · unfold parseChars
      split <;> simp_all

private def marker (k : Nat) : List Char := if k = 0 then [':', ':'] else [':']

private theorem parseChars_compressed_nil (tail : List Nat) (L : Nat)
    (htail : ∀ p ∈ tail, p < 65536) (hL : 1 ≤ L) (hsize : L + tail.length = 8) :
    parseChars (':' :: ':' :: showPieces tail) = .ok (ofPieces (List.replicate L 0 ++ tail)) := by
  show (parseLoop ((showPieces tail).length + 1) { pieceIndex := 1, compress := some 1 }
      (showPieces tail) >>= finishParse) = _
  rw [parseLoop_tail' tail _ _ htail (by simp; omega) (by omega)]
  simp only [bind, Except.bind]
  unfold finishParse
  simp only [Nat.add_sub_cancel_left]
  have := expand_writes [] tail L hL (by simpa using hsize)
  simp only [List.length_nil, Nat.zero_add, writePieces, List.nil_append] at this
  rw [this]

private theorem parseChars_compressed_cons (p : Nat) (head' tail : List Nat) (L : Nat)
    (hhead : ∀ x ∈ p :: head', x < 65536) (htail : ∀ x ∈ tail, x < 65536) (hL : 1 ≤ L)
    (hsize : (p :: head').length + L + tail.length = 8) :
    parseChars (headChars (p :: head') ++ ':' :: showPieces tail) =
      .ok (ofPieces ((p :: head') ++ List.replicate L 0 ++ tail)) := by
  have hnc : ∀ rest, headChars (p :: head') ++ ':' :: showPieces tail ≠ ':' :: rest := by
    intro rest h
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (hexDigits_ne_nil p)
    have hc := hexDigits_ne_colon p c (by rw [hcs]; simp)
    simp only [headChars, hcs, List.cons_append] at h
    exact hc (List.cons.inj h).1
  rw [parseChars_not_colon _ hnc]
  have hlen := headChars_length_ge (p :: head')
  have hk : (p :: head').length < 8 := by omega
  rw [parseLoop_head (p :: head') {} _ (showPieces tail) hhead (by simpa using hk)
    (Nat.lt_succ_self _)]
  obtain ⟨f, hfdef⟩ : ∃ f, f = (headChars (p :: head')).length + (showPieces tail).length + 1 -
      (p :: head').length := ⟨_, rfl⟩
  have hf : (headChars (p :: head') ++ ':' :: showPieces tail).length + 1 - (p :: head').length =
      f + 1 := by
    simp only [List.length_append, List.length_cons] at hfdef hlen ⊢; omega
  rw [hf, parseLoop_colon f]
  · rw [parseLoop_tail' tail _ _ htail]
    · simp only [bind, Except.bind]
      unfold finishParse
      have h3 := expand_writes (p :: head') tail L hL hsize
      simp only [Nat.zero_add] at *
      rw [Nat.add_sub_cancel_left, h3]
    · simp only [List.length_cons] at *; omega
    · simp only [List.length_cons] at *; omega
  · simp only [List.length_cons] at *; omega
  · rfl

private theorem parseChars_compressed (head tail : List Nat) (L : Nat)
    (hhead : ∀ x ∈ head, x < 65536) (htail : ∀ x ∈ tail, x < 65536) (hL : 1 ≤ L)
    (hsize : head.length + L + tail.length = 8) :
    parseChars (headChars head ++ marker head.length ++ showPieces tail) =
      .ok (ofPieces (head ++ List.replicate L 0 ++ tail)) := by
  cases head with
  | nil =>
    have := parseChars_compressed_nil tail L htail hL (by simpa using hsize)
    simpa [headChars, marker] using this
  | cons p head' =>
    have := parseChars_compressed_cons p head' tail L hhead htail hL hsize
    simpa [marker] using this

private theorem parseChars_plain (ps : List Nat) (hp : ∀ x ∈ ps, x < 65536) (hlen : ps.length = 8) :
    parseChars (showPieces ps) = .ok (ofPieces ps) := by
  have hne : ps ≠ [] := by intro h; subst h; simp at hlen
  have hnc : ∀ rest, showPieces ps ≠ ':' :: rest := by
    intro rest h
    match ps, hne, hp with
    | [x], _, _ =>
      simp only [showPieces] at h
      obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (hexDigits_ne_nil x)
      rw [hcs] at h
      exact hexDigits_ne_colon x c (by rw [hcs]; simp) (List.cons.inj h).1
    | x :: y :: ys, _, _ =>
      simp only [showPieces] at h
      obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (hexDigits_ne_nil x)
      rw [hcs] at h
      exact hexDigits_ne_colon x c (by rw [hcs]; simp) (List.cons.inj h).1
  rw [parseChars_not_colon _ hnc]
  rw [parseLoop_tail' ps _ _ hp (by simp; omega) (Nat.lt_succ_self _)]
  simp only [bind, Except.bind]
  unfold finishParse
  simp only [hlen]
  rw [writePieces_eq _ _ _ (by simp; omega)]
  simp [hlen]

private theorem printFrom_plain : ∀ (qs : List Nat) (c : Option Nat) (j : Nat) (ig : Bool),
    j + qs.length = 8 → (∀ k, c = some k → k < j) →
    (∀ q qs', qs = q :: qs' → ig = false ∨ q ≠ 0) →
    printFrom c j ig qs = showPieces qs := by
  intro qs
  induction qs with
  | nil => intro c j ig _ _ _; simp [printFrom, showPieces]
  | cons q qs' ih =>
    intro c j ig hlen hc hfirst
    have h1 : ¬ (ig && decide (q = 0)) = true := by
      rcases hfirst q qs' rfl with h | h <;> simp [h]
    have h2 : ¬ c = some j := by
      intro h; have := hc j h; omega
    rw [printFrom]
    simp only [h1, h2, ↓reduceIte]
    have ih' := ih c (j + 1) false (by simp at hlen; omega)
      (fun k hk => by have := hc k hk; omega) (fun _ _ _ => Or.inl rfl)
    rw [ih']
    cases qs' with
    | nil =>
      simp at hlen
      have : j = 7 := by omega
      simp [showPieces, this]
    | cons y qs'' =>
      simp at hlen
      have : j ≠ 7 := by omega
      simp [showPieces, this]

private theorem printFrom_skip : ∀ (m : Nat) (c : Option Nat) (j : Nat) (qs : List Nat),
    printFrom c j true (List.replicate m 0 ++ qs) = printFrom c (j + m) true qs := by
  intro m
  induction m with
  | zero => intro c j qs; simp
  | succ m ih =>
    intro c j qs
    rw [List.replicate_succ, List.cons_append, printFrom]
    simp only [Bool.true_and, decide_true, ite_true]
    rw [ih c (j + 1) qs]
    congr 1
    omega

private theorem printFrom_split : ∀ (head : List Nat) (j : Nat) (tail : List Nat) (L : Nat),
    1 ≤ L → j + head.length + L + tail.length = 8 → (∀ q qs', tail = q :: qs' → q ≠ 0) →
    printFrom (some (j + head.length)) j false (head ++ List.replicate L 0 ++ tail) =
      headChars head ++ marker (j + head.length) ++ showPieces tail := by
  intro head
  induction head with
  | nil =>
    intro j tail L hL hsize htail
    obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
    simp only [List.length_nil, Nat.add_zero, List.nil_append, headChars, marker]
    rw [List.replicate_succ, List.cons_append, printFrom]
    simp only [Bool.false_and, Bool.false_eq_true, ite_false, ite_true]
    rw [printFrom_skip, printFrom_plain tail (some j) (j + 1 + m) true
      (by simp at hsize; omega) (fun k hk => by simp at hk; omega)
      (fun q qs' h => Or.inr (htail q qs' h))]
  | cons x hs ih =>
    intro j tail L hL hsize htail
    simp only [List.length_cons] at hsize ⊢
    have e : j + (hs.length + 1) = j + 1 + hs.length := by omega
    rw [e]
    have hne : ¬ (some (j + 1 + hs.length) = some j) := by simp; omega
    have hj : j ≠ 7 := by omega
    rw [show (x :: hs) ++ List.replicate L 0 ++ tail = x :: (hs ++ List.replicate L 0 ++ tail) by simp,
      printFrom]
    simp only [Bool.false_and, Bool.false_eq_true, ite_false, hne, hj, ne_eq, not_false_eq_true,
      ite_true]
    rw [ih (j + 1) tail L hL (by omega) htail]
    simp [headChars, marker, List.append_assoc]

private theorem getElem?_append_of_some {pre : List Nat} {i v : Nat} (ys : List Nat)
    (h : pre[i]? = some v) : (pre ++ ys)[i]? = some v := by
  have hi : i < pre.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.getElem?_append_left hi]
  exact h

private theorem findCompressLoop_valid : ∀ (qs pre : List Nat) (rs rl bs bl : Nat),
    (0 < bl → pre[bs]? = some 0) → (0 < rl → pre[rs]? = some 0) →
    0 < (findCompressLoop qs pre.length rs rl bs bl).2 →
    (pre ++ qs)[(findCompressLoop qs pre.length rs rl bs bl).1]? = some 0 := by
  intro qs
  induction qs with
  | nil =>
    intro pre rs rl bs bl hb _ hpos
    simp only [findCompressLoop, List.append_nil] at hpos ⊢
    exact hb hpos
  | cons piece rest ih =>
    intro pre rs rl bs bl hb hr hpos
    rw [findCompressLoop] at hpos ⊢
    have hlen : (pre ++ [piece]).length = pre.length + 1 := by simp
    have happ : pre ++ piece :: rest = (pre ++ [piece]) ++ rest := by simp
    by_cases hp : piece = 0
    · subst hp
      simp only [ite_true]
      have hnew : (pre ++ [0])[(if rl = 0 then pre.length else rs)]? = some 0 := by
        by_cases hrl : rl = 0
        · simp [hrl]
        · simp only [hrl, ite_false]
          exact getElem?_append_of_some [0] (hr (Nat.pos_of_ne_zero hrl))
      by_cases hgt : rl + 1 > bl
      · simp only [hgt, ite_true] at hpos ⊢
        rw [happ, ← hlen]
        exact ih (pre ++ [0]) _ _ _ _ (fun _ => hnew) (fun _ => hnew) (by rw [hlen]; exact hpos)
      · simp only [hgt, ite_false] at hpos ⊢
        rw [happ, ← hlen]
        have hbl : 0 < bl := by omega
        exact ih (pre ++ [0]) _ _ _ _ (fun _ => getElem?_append_of_some [0] (hb hbl))
          (fun _ => hnew) (by rw [hlen]; exact hpos)
    · simp only [hp, ite_false] at hpos ⊢
      rw [happ, ← hlen]
      exact ih (pre ++ [piece]) _ _ _ _
        (fun h => getElem?_append_of_some [piece] (hb h)) (fun h => by omega)
        (by rw [hlen]; exact hpos)

private theorem findCompress_valid (ps : List Nat) (k : Nat) (h : findCompress ps = some k) :
    ps[k]? = some 0 := by
  unfold findCompress at h
  rcases hr : findCompressLoop ps 0 0 0 0 0 with ⟨bs, bl⟩
  rw [hr] at h
  simp only at h
  by_cases hbl : bl > 1
  · simp only [hbl, ite_true, Option.some.injEq] at h
    have := findCompressLoop_valid ps [] 0 0 0 0 (by simp) (by simp) (by simp only [List.length_nil, hr]; omega)
    simp only [List.length_nil, List.nil_append, hr] at this
    rw [← h]
    exact this
  · simp [hbl] at h

private theorem dropWhile_head_ne_zero : ∀ (l : List Nat) (q : Nat) (qs : List Nat),
    l.dropWhile (fun x => decide (x = 0)) = q :: qs → q ≠ 0 := by
  intro l
  induction l with
  | nil => intro q qs h; simp at h
  | cons x xs ih =>
    intro q qs h
    by_cases hx : x = 0
    · subst hx
      simp only [List.dropWhile_cons, decide_true, ite_true] at h
      exact ih q qs h
    · simp only [List.dropWhile_cons, hx, decide_false, ite_false, Bool.false_eq_true] at h
      have := (List.cons.inj h).1
      subst this
      exact hx

private theorem takeWhile_zero_mem : ∀ (l : List Nat) (x : Nat),
    x ∈ l.takeWhile (fun y => decide (y = 0)) → x = 0 := by
  intro l
  induction l with
  | nil => intro x h; simp at h
  | cons y ys ih =>
    intro x h
    by_cases hy : y = 0
    · subst hy
      simp only [List.takeWhile_cons, decide_true, ite_true, List.mem_cons] at h
      rcases h with h | h
      · exact h
      · exact ih x h
    · simp [hy] at h

private theorem zero_run_split (ps : List Nat) (k : Nat) (h : ps[k]? = some 0) :
    ∃ head tail L, ps = head ++ List.replicate L 0 ++ tail ∧ head.length = k ∧ 1 ≤ L ∧
      (∀ q qs', tail = q :: qs' → q ≠ 0) := by
  have hk : k < ps.length := (List.getElem?_eq_some_iff.mp h).1
  refine ⟨ps.take k, (ps.drop k).dropWhile (fun x => decide (x = 0)),
    ((ps.drop k).takeWhile (fun x => decide (x = 0))).length, ?_, ?_, ?_, ?_⟩
  · have hmid : (ps.drop k).takeWhile (fun x => decide (x = 0)) =
        List.replicate ((ps.drop k).takeWhile (fun x => decide (x = 0))).length 0 := by
      rw [List.eq_replicate_iff]
      refine ⟨rfl, fun x hx => ?_⟩
      exact takeWhile_zero_mem _ x hx
    rw [← hmid, List.append_assoc, List.takeWhile_append_dropWhile, List.take_append_drop]
  · simp [List.length_take]; omega
  · have hd : (ps.drop k)[0]? = some 0 := by simpa [List.getElem?_drop] using h
    obtain ⟨r, hr⟩ : ∃ r, ps.drop k = 0 :: r := by
      cases hdk : ps.drop k with
      | nil => simp [hdk] at hd
      | cons y r => simp [hdk] at hd; exact ⟨r, by rw [hd]⟩
    rw [hr]
    simp
  · intro q qs' hq
    exact dropWhile_head_ne_zero _ q qs' hq

private theorem ofPieces_toList (a : Ipv6) : ofPieces (a.pieces.toList.map UInt16.toNat) = a := by
  cases a with
  | mk pieces =>
    unfold ofPieces
    congr 1
    apply Vector.ext
    intro i hi
    simp

theorem parse_serialize (a : Ipv6) : parse a.serialize = .ok a := by
  have hlen : (a.pieces.toList.map UInt16.toNat).length = 8 := by simp
  have hbound : ∀ x ∈ a.pieces.toList.map UInt16.toNat, x < 65536 := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact y.toNat_lt
  unfold parse serialize
  rw [String.toList_ofList]
  generalize hps : a.pieces.toList.map UInt16.toNat = ps at hlen hbound
  have hrec : ofPieces ps = a := by rw [← hps]; exact ofPieces_toList a
  cases hc : findCompress ps with
  | none =>
    rw [printFrom_plain ps none 0 false (by omega) (by simp) (fun _ _ _ => Or.inl rfl),
      parseChars_plain ps hbound hlen, hrec]
  | some k =>
    obtain ⟨head, tail, L, hsplit, rfl, hL, htail0⟩ :=
      zero_run_split ps k (findCompress_valid ps k hc)
    have hsize : head.length + L + tail.length = 8 := by
      rw [hsplit] at hlen; simpa [Nat.add_assoc] using hlen
    have hhead : ∀ x ∈ head, x < 65536 := fun x hx => hbound x (by rw [hsplit]; simp [hx])
    have htail : ∀ x ∈ tail, x < 65536 := fun x hx => hbound x (by rw [hsplit]; simp [hx])
    have key := printFrom_split head 0 tail L hL (by omega) htail0
    rw [← hsplit, Nat.zero_add] at key
    rw [key, parseChars_compressed head tail L hhead htail hL hsize, ← hsplit, hrec]

end Urllib.Host.Ipv6
