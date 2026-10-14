import Goose.GIR.Validate
import Goose.GIR.Lemmas
import Goose.GIR.Sound

/-!
Soundness statements for GIR bounds evidence. The executable checker is kept
separate from these propositions: this file extracts the structural
certificate derivation and relates the unchecked index operation to the
checked operation when its three runtime facts hold.
-/

namespace Goose.Proofs.Bounds

open Goose.Core Goose.GIR

def FactSetValid (m : GIR.Module) (f : Func) (vt : Array (Option VTy))
    (facts : Facts) : Prop :=
  facts.Nodup ∧ ∀ fact ∈ facts, fact.wellTyped m f vt = true

def ClaimsDerived (claimed derived : Facts) : Prop :=
  ∀ fact ∈ claimed, fact ∈ derived

def BlockEvidenceValid (m : GIR.Module) (f : Func) (certificate : FactCertificate)
    (blockId : BlockId) : Prop :=
  match f.blocks[blockId]? with
  | none => False
  | some block =>
    ∃ outgoing, transferBlock m f (certificate[blockId]?.getD []) block = .ok outgoing ∧
      match block.lastTerm? with
      | some (.br target args) =>
        ClaimsDerived (certificate[target]?.getD []) (edgeFacts f outgoing none target args)
      | some (.condbr condition yes yesArgs no noArgs) =>
        ClaimsDerived (certificate[yes]?.getD [])
            (edgeFacts f outgoing (some condition) yes yesArgs) ∧
          ClaimsDerived (certificate[no]?.getD [])
            (edgeFacts f outgoing none no noArgs)
      | _ => True

structure CertificateValid (m : GIR.Module) (f : Func) (vt : Array (Option VTy))
    (certificate : FactCertificate) : Prop where
  blockCount : certificate.size = f.blocks.size
  entryEmpty : certificate[0]?.getD [] = []
  factSets : ∀ facts ∈ certificate.toList, FactSetValid m f vt facts
  blocks : ∀ blockId < f.blocks.size, BlockEvidenceValid m f certificate blockId

inductive FunctionEvidenceValid (m : GIR.Module) (f : Func) (vt : Array (Option VTy)) : Prop
  | absent : f.certificate = none → hasProvenIndex f = false → FunctionEvidenceValid m f vt
  | present (certificate : FactCertificate) : f.certificate = some certificate →
      CertificateValid m f vt certificate → FunctionEvidenceValid m f vt

private theorem checkEvery_ok {xs : List α} {check : α → Except String Unit}
    (h : checkEvery xs check = .ok ()) : ∀ x ∈ xs, check x = .ok () := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
    simp only [checkEvery] at h
    cases hc : check head with
    | error e => simp [hc, bind, Except.bind] at h
    | ok u =>
      cases u
      have ht : checkEvery tail check = .ok () := by
        simpa [hc, bind, Except.bind] using h
      intro x hx
      simp only [List.mem_cons] at hx
      cases hx with
      | inl he => simpa [he] using hc
      | inr hm => exact ih ht x hm

private theorem checkSubset_ok {claimed derived : Facts}
    (h : checkSubset claimed derived = .ok ()) : ClaimsDerived claimed derived := by
  unfold checkSubset at h
  split at h
  · rename_i hall
    intro fact hfact
    have := List.all_eq_true.mp hall fact hfact
    simpa using this
  · contradiction

private theorem checkFactSet_ok {m : GIR.Module} {f : Func} {vt : Array (Option VTy)}
    {facts : Facts} (h : checkFactSet m f vt facts = .ok ()) : FactSetValid m f vt facts := by
  by_cases hn : facts.Nodup
  · by_cases hw : facts.all (Fact.wellTyped m f vt) = true
    · constructor
      · exact hn
      · exact List.all_eq_true.mp hw
    · simp [checkFactSet, hn, hw] at h
  · simp [checkFactSet, hn, bind, Except.bind] at h

private theorem checkBlockEvidence_ok {m : GIR.Module} {f : Func}
    {certificate : FactCertificate} {blockId : BlockId}
    (h : checkBlockEvidence m f certificate blockId = .ok ()) :
    BlockEvidenceValid m f certificate blockId := by
  unfold checkBlockEvidence at h
  cases hb : f.blocks[blockId]? with
  | none => simp [hb] at h
  | some block =>
    simp only [hb] at h
    cases ht : transferBlock m f (certificate[blockId]?.getD []) block with
    | error e => simp [ht, bind, Except.bind] at h
    | ok outgoing =>
      simp only [BlockEvidenceValid, hb]
      refine ⟨outgoing, ht, ?_⟩
      cases term : block.lastTerm? with
      | none => trivial
      | some t =>
        cases t with
        | br target args =>
          exact checkSubset_ok (by
            simpa [ht, term, bind, Except.bind, pure, Except.pure] using h)
        | condbr condition yes yesArgs no noArgs =>
          have h' : (do
              checkSubset (certificate[yes]?.getD [])
                (edgeFacts f outgoing (some condition) yes yesArgs)
              checkSubset (certificate[no]?.getD [])
                (edgeFacts f outgoing none no noArgs)) = .ok () := by
            simpa [ht, term, bind, Except.bind, pure, Except.pure] using h
          rcases Goose.GIR.bind_ok h' with ⟨u, hy, hn⟩
          cases u
          exact ⟨checkSubset_ok hy, checkSubset_ok hn⟩
        | ret _ _ => trivial
        | abort _ _ => trivial
        | exit _ _ => trivial
        | unreachable => trivial

/-- The structural part of certificate soundness: an accepted executable
evidence check supplies a declarative derivation for every claimed fact set
and CFG edge. Relating the derivation to facts in every reachable runtime
frame is a separate whole-run obligation. -/
theorem checkEvidence_sound {m : GIR.Module} {f : Func} {vt : Array (Option VTy)}
    (h : checkEvidence m f vt = .ok ()) : FunctionEvidenceValid m f vt := by
  unfold checkEvidence at h
  cases hc : f.certificate with
  | none =>
    by_cases hp : hasProvenIndex f
    · simp [hc, hp] at h
    · exact .absent hc (Bool.eq_false_iff.mpr hp)
  | some certificate =>
    simp only [hc] at h
    by_cases hs : certificate.size = f.blocks.size
    · by_cases he : certificate[0]?.getD [] = []
      · have hsb : (certificate.size == f.blocks.size) = true := beq_iff_eq.mpr hs
        have heb : (certificate[0]?.getD [] == []) = true := beq_iff_eq.mpr he
        simp [hsb, heb] at h
        cases hf : checkEvery certificate.toList (checkFactSet m f vt) with
        | error e => simp [hf, bind, Except.bind] at h
        | ok u =>
          cases u
          have hb : checkEvery (List.range f.blocks.size)
              (checkBlockEvidence m f certificate) = .ok () := by
            simpa [hf, bind, Except.bind] using h
          refine .present certificate hc ⟨hs, he, ?_, ?_⟩
          · intro facts hmem
            exact checkFactSet_ok (checkEvery_ok hf facts hmem)
          · intro blockId hlt
            exact checkBlockEvidence_ok
              (checkEvery_ok hb blockId (List.mem_range.mpr hlt))
      · have hsb : (certificate.size == f.blocks.size) = true := beq_iff_eq.mpr hs
        have heb : (certificate[0]?.getD [] == []) = false := beq_eq_false_iff_ne.mpr he
        simp [hsb, heb, bind, Except.bind] at h
    · have hsb : (certificate.size == f.blocks.size) = false := beq_eq_false_iff_ne.mpr hs
      simp [hsb, bind, Except.bind] at h

def IntAt (fr : Frame) (value : ValueId) (number : Int) : Prop :=
  ∃ ty, fr.vals[value]? = some (.val (.int ty number))

def RefAt (fr : Frame) (value : ValueId) (loc : Loc) : Prop :=
  fr.vals[value]? = some (.val (.ref loc))

def ViewAt (fr : Frame) (value : ValueId) (view : ViewVal) : Prop :=
  fr.vals[value]? = some (.view view)

def ArrayLenAt (state : St) (loc : Loc) (len : Nat) : Prop :=
  ∃ value resizable,
    readLoc loc state = .ok value state ∧
    expectArray value state = .ok (len, resizable) state

private theorem RefAt.unique {fr : Frame} {value : ValueId} {a b : Loc}
    (ha : RefAt fr value a) (hb : RefAt fr value b) : a = b := by
  unfold RefAt at ha hb
  rw [ha] at hb
  cases hb
  rfl

private theorem ArrayLenAt.unique {state : St} {loc : Loc} {a b : Nat}
    (ha : ArrayLenAt state loc a) (hb : ArrayLenAt state loc b) : a = b := by
  rcases ha with ⟨va, ra, hreadA, harrayA⟩
  rcases hb with ⟨vb, rb, hreadB, harrayB⟩
  rw [hreadA] at hreadB
  cases hreadB
  rw [harrayA] at harrayB
  cases harrayB
  rfl

def FactHolds (fr : Frame) (state : St) : Fact → Prop
  | .ge0 i => ∃ value, IntAt fr i value ∧ 0 ≤ value
  | .lt i n => ∃ value bound, IntAt fr i value ∧ IntAt fr n bound ∧ value < bound
  | .lenGe reference n => ∃ loc bound len,
      RefAt fr reference loc ∧ IntAt fr n bound ∧ ArrayLenAt state loc len ∧ bound ≤ (len : Int)
  | .viewLenGe v n => ∃ view bound,
      ViewAt fr v view ∧ IntAt fr n bound ∧ bound ≤ (view.len : Int)

def FactsHold (fr : Frame) (state : St) (facts : Facts) : Prop :=
  ∀ fact ∈ facts, FactHolds fr state fact

def IndexFactsHold (fr : Frame) (view index bound : ValueId) : Prop :=
  ∃ vw indexValue boundValue,
    ViewAt fr view vw ∧ IntAt fr index indexValue ∧ IntAt fr bound boundValue ∧
    0 ≤ indexValue ∧ indexValue < boundValue ∧ boundValue ≤ (vw.len : Int)

private theorem IntAt.unique {fr : Frame} {value : ValueId} {a b : Int}
    (ha : IntAt fr value a) (hb : IntAt fr value b) : a = b := by
  rcases ha with ⟨ta, ha⟩
  rcases hb with ⟨tb, hb⟩
  rw [ha] at hb
  cases hb
  rfl

/-- A syntactically justified proven index carries one common runtime bound
when all facts replayed by the checker hold. -/
theorem provesIndex_sound {fr : Frame} {state : St} {facts : Facts}
    {view index : ValueId} (hh : FactsHold fr state facts)
    (hp : provesIndex facts view index = true) :
    ∃ bound, IndexFactsHold fr view index bound := by
  simp only [provesIndex, Bool.and_eq_true] at hp
  rcases hp with ⟨hge, hany⟩
  have ge := hh (.ge0 index) (of_decide_eq_true hge)
  simp only [List.any_eq_true] at hany
  rcases hany with ⟨fact, hmem, hfact⟩
  cases fact with
  | ge0 i => simp at hfact
  | lt i n => simp at hfact
  | lenGe reference n => simp at hfact
  | viewLenGe found bound =>
    simp only at hfact
    rw [Bool.and_eq_true] at hfact
    have hv : found = view := beq_iff_eq.mp hfact.1
    subst found
    have hltMem : Fact.lt index bound ∈ facts :=
      of_decide_eq_true hfact.2
    have viewFact := hh (.viewLenGe view bound) hmem
    have ltFact := hh (.lt index bound) hltMem
    rcases ge with ⟨indexValue, hindex, hnonneg⟩
    rcases viewFact with ⟨vw, boundValue, hview, hboundView, hlen⟩
    rcases ltFact with ⟨indexValue', boundValue', hindex', hboundLt, hlt⟩
    have hi : indexValue' = indexValue := IntAt.unique hindex' hindex
    have hn : boundValue' = boundValue := IntAt.unique hboundLt hboundView
    subst indexValue'
    subst boundValue'
    exact ⟨bound, vw, indexValue, boundValue, hview, hindex, hboundView,
      hnonneg, hlt, hlen⟩

def withCell (fr : Frame) (value : ValueId) (cell : RVal) : Frame :=
  { fr with vals := fr.vals.insert value cell }

/-- F-CONST is sound in the runtime fact interpretation. -/
theorem f_const_sound {fr : Frame} {state : St} {result : ValueId}
    {value : Int} (h : 0 ≤ value) :
    FactHolds (withCell fr result (.val (.int .i64 value))) state (.ge0 result) := by
  refine ⟨value, ?_, h⟩
  exact ⟨.i64, by simp [withCell]⟩

/-- F-LEN is sound after a successful array-length read. -/
theorem f_len_sound {fr : Frame} {state : St} {reference result : ValueId}
    {loc : Loc} {len : Nat} (fresh : result ≠ reference)
    (href : RefAt fr reference loc) (hlen : ArrayLenAt state loc len) :
    FactHolds (withCell fr result (.val (.int .i64 len))) state (.ge0 result) ∧
    FactHolds (withCell fr result (.val (.int .i64 len))) state
      (.lenGe reference result) := by
  constructor
  · exact f_const_sound (Int.natCast_nonneg len)
  · refine ⟨loc, len, len, ?_, ?_, hlen, by simp⟩
    · unfold RefAt at href ⊢
      simpa [withCell, Std.HashMap.getElem?_insert,
        beq_eq_false_iff_ne.mpr fresh] using href
    · exact ⟨.i64, by simp [withCell]⟩

/-- F-SNAP is sound after sampling the same reference named by `lenGe`. -/
theorem f_snap_sound {fr : Frame} {state : St} {reference bound result : ValueId}
    {loc : Loc} {len start : Nat} {resizable : Bool}
    (freshBound : result ≠ bound) (hrefNow : RefAt fr reference loc)
    (harrayNow : ArrayLenAt state loc len)
    (hlen : FactHolds fr state (.lenGe reference bound)) :
    FactHolds
      (withCell fr result (.view ⟨loc, start, len, resizable⟩)) state
      (.viewLenGe result bound) := by
  rcases hlen with ⟨foundLoc, boundValue, foundLen, href, hbound, harray, hle⟩
  have hloc : foundLoc = loc := RefAt.unique href hrefNow
  subst foundLoc
  have hlength : foundLen = len := ArrayLenAt.unique harray harrayNow
  subst foundLen
  refine ⟨⟨loc, start, len, resizable⟩, boundValue, ?_, ?_, hle⟩
  · unfold ViewAt
    simp [withCell]
  · rcases hbound with ⟨ty, hbound⟩
    exact ⟨ty, by simpa [withCell, Std.HashMap.getElem?_insert,
      beq_eq_false_iff_ne.mpr freshBound] using hbound⟩

/-- F-CMP is sound on the true edge of a signed i64 less-than comparison. -/
theorem f_cmp_sound {fr : Frame} {state : St} {left right : ValueId}
    {a b : Int} (ha : IntAt fr left a) (hb : IntAt fr right b) (hlt : a < b) :
    FactHolds fr state (.lt left right) :=
  ⟨a, b, ha, hb, hlt⟩

/-- The semantic core of TH-BCE-01: when the three certified runtime facts
hold, an unchecked index step is exactly the checked index step. -/
theorem indexProven_eq_checked_of_facts {cx : FnCtx} {fr : Frame}
    {view index bound : ValueId}
    (h : IndexFactsHold fr view index bound) :
    execPure cx fr (.indexProven view index) =
      execPure cx fr (.indexChecked view index none) := by
  rcases h with ⟨vw, indexValue, boundValue,
    hview, hindex, hbound, hnonneg, hlt, hlen⟩
  rcases hindex with ⟨indexTy, hindex⟩
  rcases hbound with ⟨boundTy, hbound⟩
  unfold ViewAt at hview
  have hin : indexValue < (vw.len : Int) := by omega
  funext state
  simp [execPure, getView, getCell, getVal, hview, hindex, expectInt,
    hnonneg, hin, bind, M.bind', pure, M.pure']

/-- Replacing one certified unchecked instruction by its checked form preserves
the instruction's result, frame update and arbitrary continuation. -/
theorem exec_indexProven_eq_checked {fuel : Nat} {cx : FnCtx} {fr : Frame}
    {state : St} {facts : Facts} {result view index : ValueId} {rest : List Inst}
    (hh : FactsHold fr state facts) (hp : provesIndex facts view index = true) :
    exec (fuel + 1) cx fr (.def result (.indexProven view index) :: rest) =
      exec (fuel + 1) cx fr (.def result (.indexChecked view index none) :: rest) := by
  obtain ⟨bound, hbound⟩ := provesIndex_sound hh hp
  have hop := indexProven_eq_checked_of_facts (cx := cx) hbound
  simp only [exec, execOp]
  rw [hop]

end Goose.Proofs.Bounds
