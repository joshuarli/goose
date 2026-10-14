import Goose.Proofs.Bounds

namespace Goose.Proofs.Bounds

open Goose.Core Goose.GIR

theorem FactsHold.empty (fr : Frame) (state : St) : FactsHold fr state [] := by
  simp [FactsHold]

theorem FactsHold.subset {fr : Frame} {state : St} {claimed derived : Facts}
    (hold : FactsHold fr state derived) (subset : ClaimsDerived claimed derived) :
    FactsHold fr state claimed := fun fact member => hold fact (subset fact member)

theorem FactsHold.add {fr : Frame} {state : St} {facts : Facts} {fact : Fact}
    (hold : FactsHold fr state facts) (newFact : FactHolds fr state fact) :
    FactsHold fr state (addFact facts fact) := by
  unfold addFact
  split
  · exact hold
  · intro found member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact hold found member
    · exact newFact

theorem FactHolds.sameCells {fr next : Frame} {state : St} {fact : Fact}
    (cells : ∀ value, fact.mentions value = true → next.vals[value]? = fr.vals[value]?)
    (hold : FactHolds fr state fact) : FactHolds next state fact := by
  cases fact with
  | ge0 i =>
    rcases hold with ⟨number, ⟨ty, cell⟩, nonneg⟩
    exact ⟨number, ⟨ty, by rw [cells i (by simp [Fact.mentions])]; exact cell⟩, nonneg⟩
  | lt i n =>
    rcases hold with ⟨number, bound, ⟨ity, icell⟩, ⟨nty, ncell⟩, less⟩
    exact ⟨number, bound,
      ⟨ity, by rw [cells i (by simp [Fact.mentions])]; exact icell⟩,
      ⟨nty, by rw [cells n (by simp [Fact.mentions])]; exact ncell⟩, less⟩
  | lenGe r n =>
    rcases hold with ⟨loc, bound, len, ref, ⟨ty, cell⟩, length, less⟩
    exact ⟨loc, bound, len,
      by unfold RefAt at ref ⊢; rw [cells r (by simp [Fact.mentions])]; exact ref,
      ⟨ty, by rw [cells n (by simp [Fact.mentions])]; exact cell⟩, length, less⟩
  | viewLenGe v n =>
    rcases hold with ⟨view, bound, atView, ⟨ty, cell⟩, less⟩
    exact ⟨view, bound,
      by unfold ViewAt at atView ⊢; rw [cells v (by simp [Fact.mentions])]; exact atView,
      ⟨ty, by rw [cells n (by simp [Fact.mentions])]; exact cell⟩, less⟩

theorem FactsHold.killValue {fr : Frame} {state : St} {facts : Facts}
    (hold : FactsHold fr state facts) (value : ValueId) (cell : RVal) :
    FactsHold (withCell fr value cell) state (Goose.GIR.killValue facts value) := by
  intro fact member
  obtain ⟨member, survives⟩ := List.mem_filter.mp member
  apply FactHolds.sameCells (hold := hold fact member)
  intro other mentioned
  have different : value ≠ other := by
    intro same
    subst other
    simp [mentioned] at survives
  simp [withCell, Std.HashMap.getElem?_insert, beq_eq_false_iff_ne.mpr different]

theorem FactHolds.withoutLength {fr next : Frame} {state after : St} {fact : Fact}
    (cells : next.vals = fr.vals) (notLength : ∀ r n, fact ≠ .lenGe r n)
    (hold : FactHolds fr state fact) : FactHolds next after fact := by
  cases fact with
  | ge0 i => simpa [FactHolds, IntAt, cells] using hold
  | lt i n => simpa [FactHolds, IntAt, cells] using hold
  | lenGe r n => exact False.elim (notLength r n rfl)
  | viewLenGe v n => simpa [FactHolds, ViewAt, IntAt, cells] using hold

theorem FactsHold.killLengths {fr next : Frame} {state after : St} {facts : Facts}
    (hold : FactsHold fr state facts) (cells : next.vals = fr.vals) :
    FactsHold next after (Goose.GIR.killLengths facts) := by
  intro fact member
  obtain ⟨member, survives⟩ := List.mem_filter.mp member
  apply FactHolds.withoutLength cells (hold := hold fact member)
  intro r n same
  subst fact
  simp at survives

theorem FactsHold.bindParams {fr : Frame} {state : St} {facts : Facts}
    (hold : FactsHold fr state facts) : ∀ {params : List (ValueId × VTy)}
    {args : List RVal} {next : Frame},
    Goose.GIR.bindParams fr params args state = .ok next state →
    FactsHold next state (facts.filter fun fact => !(params.any fun param => fact.mentions param.1)) := by
  intro params
  induction params generalizing fr facts with
  | nil =>
    intro args next result
    simp [Goose.GIR.bindParams, pure, M.pure'] at result
    cases result
    intro fact member
    exact hold fact (List.mem_filter.mp member).1
  | cons param params ih =>
    intro args next result
    cases args with
    | nil =>
      simp [Goose.GIR.bindParams, pure, M.pure'] at result
      cases result
      intro fact member
      exact hold fact (List.mem_filter.mp member).1
    | cons arg args =>
      have result' : Goose.GIR.bindParams (withCell fr param.1 arg) params args state = .ok next state := by
        simpa [Goose.GIR.bindParams, setCell, withCell, bind, M.bind', pure, M.pure'] using result
      have preserved := ih (FactsHold.killValue hold param.1 arg) result'
      intro fact member
      apply preserved fact
      obtain ⟨member, survives⟩ := List.mem_filter.mp member
      simp [List.any_cons] at survives
      apply List.mem_filter.mpr
      constructor
      · exact List.mem_filter.mpr ⟨member, by simpa [killValue] using survives.1⟩
      · simpa using survives.2

theorem bindParams_state {fr next : Frame} {state after : St}
    {params : List (ValueId × VTy)} {args : List RVal}
    (result : Goose.GIR.bindParams fr params args state = .ok next after) : after = state := by
  induction params generalizing fr args with
  | nil =>
    simp [Goose.GIR.bindParams, pure, M.pure'] at result
    exact result.2.symm
  | cons param params ih =>
    cases args with
    | nil =>
      simp [Goose.GIR.bindParams, pure, M.pure'] at result
      exact result.2.symm
    | cons arg args =>
      apply ih (fr := withCell fr param.1 arg) (args := args)
      simpa [Goose.GIR.bindParams, setCell, withCell, bind, M.bind', pure, M.pure'] using result

theorem FactsHold.enterBlock {f : Func} {fr next : Frame} {state after : St}
    {facts : Facts} {target : BlockId} {args : List RVal} {insts : List Inst}
    (hold : FactsHold fr state facts)
    (result : Goose.GIR.enterBlock f fr target args state = .ok (insts, next) after) :
    FactsHold next after (translateEdge f facts target []) := by
  unfold Goose.GIR.enterBlock at result
  cases blockAt : f.blocks[target]? with
  | none => simp [blockAt, fault, M.stop] at result
  | some block =>
    simp only [blockAt] at result
    split at result
    · rename_i arity
      simp only [bind_apply] at result
      cases bound : Goose.GIR.bindParams fr block.params args state with
      | stop reason stopped => simp [bound] at result
      | ok frame endState =>
        simp only [bound, pure_apply, Res.ok.injEq, Prod.mk.injEq] at result
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := result
        have same := bindParams_state bound
        subst endState
        simpa [translateEdge, blockAt, List.any_map, Function.comp_def] using FactsHold.bindParams hold bound
    · simp [fault, M.stop] at result

private def Returns (computation : M α) (property : α → Prop) : Prop :=
  ∀ state value after, computation state = .ok value after → property value

private theorem returns_bind {computation : M α} {next : α → M β} {property : β → Prop}
    (holds : ∀ value, Returns (next value) property) :
    Returns (computation >>= next) property := by
  intro state value after result
  rw [bind_apply] at result
  cases evaluated : computation state with
  | stop reason stopped => simp [evaluated] at result
  | ok intermediate middle =>
    exact holds intermediate middle value after (by simpa [evaluated] using result)

private theorem returns_pure {value : α} {property : α → Prop} (holds : property value) :
    Returns (pure value) property := by
  intro state found after result
  simp only [pure_apply, Res.ok.injEq] at result
  simpa [← result.1] using holds

private theorem returns_fault {reason : FaultKind} {property : α → Prop} :
    Returns (fault reason) property := by
  intro state value after result
  simp [fault, M.stop] at result

private theorem returns_abort {reason : AbortKind} {origin : Option OriginId}
    {property : α → Prop} : Returns (abortAtOrg reason origin) property := by
  intro state value after result
  cases origin <;> simp [abortAtOrg, fault, abortAt, M.stop] at result

theorem execEff_cells {f : Func} {fr next : Frame} {effect : Effect} {state after : St}
    (result : execEff f fr effect state = .ok next after) : next.vals = fr.vals := by
  have holds : Returns (execEff f fr effect) (fun next => next.vals = fr.vals) := by
    cases effect with
    | slotInit =>
      simp only [execEff]
      iterate 3 (apply returns_bind; intro)
      exact returns_pure rfl
    | store =>
      simp only [execEff]
      iterate 4 (apply returns_bind; intro)
      exact returns_pure rfl
    | append =>
      simp only [execEff]
      iterate 6 (apply returns_bind; intro)
      exact returns_pure rfl
    | clear =>
      simp only [execEff]
      iterate 3 (apply returns_bind; intro)
      exact returns_pure rfl
    | enter =>
      simp only [execEff]
      apply returns_bind
      intro scopeInstance
      exact returns_pure rfl
    | print =>
      simp only [execEff]
      iterate 2 (apply returns_bind; intro)
      exact returns_pure rfl
    | popN =>
      simp only [execEff]
      iterate 5 (apply returns_bind; intro)
      split
      · exact returns_abort
      · apply returns_bind
        intro ignored
        exact returns_pure rfl
    | replace =>
      simp only [execEff]
      iterate 3 (apply returns_bind; intro)
      split
      · apply returns_bind
        intro ignored
        exact returns_pure rfl
      · apply returns_bind
        intro impossible
        exact returns_pure rfl
    | leave =>
      simp only [execEff]
      split
      · split
        · apply returns_bind
          intro ignored
          exact returns_pure rfl
        · exact returns_fault
      · exact returns_fault
    | resize r size fill origin =>
      cases fill with
      | none =>
        simp only [execEff, pure_bind]
        iterate 5 (apply returns_bind; intro)
        split
        · exact returns_abort
        · split
          · apply returns_bind
            intro ignored
            exact returns_pure rfl
          · split
            · exact returns_pure rfl
            · first
              | exact returns_abort
              | exact returns_bind fun _ => returns_bind fun _ => returns_pure rfl
      | some value =>
        simp only [execEff, pure_bind]
        iterate 5 (apply returns_bind; intro)
        apply returns_bind
        intro len
        split
        · exact returns_abort
        · split
          · apply returns_bind
            intro ignored
            exact returns_pure rfl
          · split
            · exact returns_pure rfl
            · first
              | exact returns_abort
              | exact returns_bind fun _ => returns_bind fun _ => returns_pure rfl
  exact holds state next after result

theorem FactsHold.mutatingEffect {f : Func} {fr next : Frame} {effect : Effect}
    {state after : St} {facts : Facts} (hold : FactsHold fr state facts)
    (result : execEff f fr effect state = .ok next after) :
    FactsHold next after (Goose.GIR.killLengths facts) :=
  FactsHold.killLengths hold (execEff_cells result)

theorem FactsHold.mutatingDef {fr : Frame} {state after : St} {facts : Facts}
    (hold : FactsHold fr state facts) (result : ValueId) (cell : RVal) :
    FactsHold (withCell fr result cell) after
      (Goose.GIR.killLengths (Goose.GIR.killValue facts result)) :=
  FactsHold.killLengths (FactsHold.killValue hold result cell) rfl

theorem FactsHold.claimedEdge {f : Func} {fr next : Frame} {state after : St}
    {facts claimed : Facts} {target : BlockId} {args : List RVal} {insts : List Inst}
    (hold : FactsHold fr state facts)
    (derived : ClaimsDerived claimed (translateEdge f facts target []))
    (result : Goose.GIR.enterBlock f fr target args state = .ok (insts, next) after) :
    FactsHold next after claimed :=
  FactsHold.subset (FactsHold.enterBlock hold result) derived

private theorem success_bind {computation : M α} {next : α → M β}
    {state after : St} {result : β}
    (success : (computation >>= next) state = .ok result after) :
    ∃ value middle, computation state = .ok value middle ∧ next value middle = .ok result after := by
  rw [bind_apply] at success
  cases evaluated : computation state with
  | stop reason stopped => simp [evaluated] at success
  | ok value middle => exact ⟨value, middle, rfl, by simpa [evaluated] using success⟩

theorem getCell_success {fr : Frame} {id : ValueId} {state after : St} {cell : RVal}
    (success : getCell fr id state = .ok cell after) :
    fr.vals[id]? = some cell ∧ after = state := by
  unfold getCell at success
  cases found : fr.vals[id]? with
  | none => simp [found, fault, M.stop] at success
  | some value =>
    simp only [found, pure_apply, Res.ok.injEq] at success
    exact ⟨by simp [← success.1], success.2.symm⟩

theorem getVal_success {fr : Frame} {id : ValueId} {state after : St} {value : Val}
    (success : getVal fr id state = .ok value after) :
    fr.vals[id]? = some (.val value) ∧ after = state := by
  unfold getVal at success
  obtain ⟨cell, middle, read, success⟩ := success_bind success
  obtain ⟨found, same⟩ := getCell_success read
  subst middle
  cases cell with
  | val cell =>
    simp only [pure_apply, Res.ok.injEq] at success
    exact ⟨by simp [← success.1, found], success.2.symm⟩
  | view cell => simp [fault, M.stop] at success

theorem getView_success {fr : Frame} {id : ValueId} {state after : St} {value : ViewVal}
    (success : getView fr id state = .ok value after) :
    fr.vals[id]? = some (.view value) ∧ after = state := by
  unfold getView at success
  obtain ⟨cell, middle, read, success⟩ := success_bind success
  obtain ⟨found, same⟩ := getCell_success read
  subst middle
  cases cell with
  | val cell => simp [fault, M.stop] at success
  | view cell =>
    simp only [pure_apply, Res.ok.injEq] at success
    exact ⟨by simp [← success.1, found], success.2.symm⟩

theorem expectRef_success {value : Val} {state after : St} {loc : Loc}
    (success : expectRef value state = .ok loc after) : value = .ref loc ∧ after = state := by
  cases value <;> simp [expectRef, pure, M.pure', fault, M.stop] at success
  obtain ⟨rfl, rfl⟩ := success
  exact ⟨rfl, rfl⟩

theorem readLoc_state {loc : Loc} {state after : St} {value : Val}
    (success : readLoc loc state = .ok value after) : after = state := by
  unfold readLoc at success
  split at success
  · exact (Res.ok.inj success).2.symm
  · contradiction

theorem expectArray_state {value : Val} {state after : St} {length : Nat × Bool}
    (success : expectArray value state = .ok length after) : after = state := by
  cases value <;> simp [expectArray, pure, M.pure', fault, M.stop] at success
  all_goals exact success.2.symm

theorem arrayLen_success {cx : FnCtx} {fr : Frame} {reference : ValueId}
    {state after : St} {cell : RVal}
    (success : execPure cx fr (.arrayLen reference) state = .ok cell after) :
    ∃ loc len, RefAt fr reference loc ∧ ArrayLenAt state loc len ∧
      cell = .val (.int .i64 len) ∧ after = state := by
  simp only [execPure] at success
  obtain ⟨value, first, hvalue, success⟩ := success_bind success
  obtain ⟨loc, second, href, success⟩ := success_bind success
  obtain ⟨array, third, harray, success⟩ := success_bind success
  obtain ⟨length, fourth, hlength, success⟩ := success_bind success
  obtain ⟨atValue, same⟩ := getVal_success hvalue
  subst first
  obtain ⟨rfl, same⟩ := expectRef_success href
  subst second
  have same := readLoc_state harray
  subst third
  have same := expectArray_state hlength
  subst fourth
  simp only [pure_apply, Res.ok.injEq] at success
  refine ⟨loc, length.1, atValue, ⟨array, length.2, harray, hlength⟩, success.1.symm,
    success.2.symm⟩

theorem arrayLen_facts {cx : FnCtx} {fr : Frame} {reference result : ValueId}
    {state after : St} {cell : RVal} (fresh : result ≠ reference)
    (success : execPure cx fr (.arrayLen reference) state = .ok cell after) :
    FactHolds (withCell fr result cell) after (.ge0 result) ∧
      FactHolds (withCell fr result cell) after (.lenGe reference result) := by
  obtain ⟨loc, len, ref, length, rfl, rfl⟩ := arrayLen_success success
  exact f_len_sound fresh ref length

theorem snapshot_success {cx : FnCtx} {fr : Frame} {reference : ValueId}
    {mode : SnapshotMode} {state after : St} {cell : RVal}
    (success : execPure cx fr (.snapshot mode reference) state = .ok cell after) :
    ∃ loc len resizable, RefAt fr reference loc ∧ ArrayLenAt state loc len ∧
      cell = .view ⟨loc, 0, len, resizable⟩ ∧ after = state := by
  simp only [execPure] at success
  obtain ⟨value, first, hvalue, success⟩ := success_bind success
  obtain ⟨loc, second, href, success⟩ := success_bind success
  obtain ⟨array, third, harray, success⟩ := success_bind success
  obtain ⟨length, fourth, hlength, success⟩ := success_bind success
  obtain ⟨atValue, same⟩ := getVal_success hvalue
  subst first
  obtain ⟨rfl, same⟩ := expectRef_success href
  subst second
  have same := readLoc_state harray
  subst third
  have same := expectArray_state hlength
  subst fourth
  simp only [pure_apply, Res.ok.injEq] at success
  exact ⟨loc, length.1, length.2, atValue, ⟨array, length.2, harray, hlength⟩,
    success.1.symm, success.2.symm⟩

theorem snapshot_fact {cx : FnCtx} {fr : Frame} {reference result bound : ValueId}
    {mode : SnapshotMode} {state after : St} {cell : RVal} (fresh : result ≠ bound)
    (hold : FactHolds fr state (.lenGe reference bound))
    (success : execPure cx fr (.snapshot mode reference) state = .ok cell after) :
    FactHolds (withCell fr result cell) after (.viewLenGe result bound) := by
  obtain ⟨loc, len, resizable, ref, length, rfl, rfl⟩ := snapshot_success success
  exact f_snap_sound fresh ref length hold

theorem constInt_fact {cx : FnCtx} {fr : Frame} {result : ValueId} {number : Int}
    {state after : St} {cell : RVal} (nonnegative : 0 ≤ number)
    (success : execPure cx fr (.constInt .i64 number) state = .ok cell after) :
    FactHolds (withCell fr result cell) after (.ge0 result) := by
  simp only [execPure, pure_apply, Res.ok.injEq] at success
  obtain ⟨rfl, rfl⟩ := success
  exact f_const_sound nonnegative

private def StateStable (computation : M α) : Prop :=
  ∀ state value after, computation state = .ok value after → after = state

private theorem StateStable.pure (value : α) : StateStable (pure value) := by
  intro state found after success
  exact (Res.ok.inj success).2.symm

private theorem StateStable.fault (kind : FaultKind) : StateStable (fault kind : M α) := by
  intro state value after success
  simp [Goose.Core.fault, M.stop] at success

private theorem StateStable.abort (kind : AbortKind) (origin : Option OriginId) :
    StateStable (abortAtOrg kind origin : M α) := by
  intro state value after success
  cases origin <;> simp [abortAtOrg, Goose.Core.fault, abortAt, M.stop] at success

private theorem StateStable.bind {computation : M α} {next : α → M β}
    (first : StateStable computation) (rest : ∀ value, StateStable (next value)) :
    StateStable (computation >>= next) := by
  intro state value after success
  obtain ⟨intermediate, middle, evaluated, success⟩ := success_bind success
  exact (rest intermediate middle value after success).trans
    (first state intermediate middle evaluated)

private theorem stable_getVal (fr : Frame) (id : ValueId) : StateStable (getVal fr id) :=
  fun _ _ _ success => (getVal_success success).2

private theorem stable_getView (fr : Frame) (id : ValueId) : StateStable (getView fr id) :=
  fun _ _ _ success => (getView_success success).2

private theorem stable_readLoc (loc : Loc) : StateStable (readLoc loc) :=
  fun _ _ _ success => readLoc_state success

private theorem stable_expectInt (value : Val) : StateStable (expectInt value) := by
  cases value <;> first | exact StateStable.pure _ | exact StateStable.fault _

private theorem stable_expectBool (value : Val) : StateStable (expectBool value) := by
  cases value <;> first | exact StateStable.pure _ | exact StateStable.fault _

private theorem stable_expectRef (value : Val) : StateStable (expectRef value) :=
  fun _ _ _ success => (expectRef_success success).2

private theorem stable_expectSlice (value : Val) : StateStable (expectSlice value) := by
  cases value <;> first | exact StateStable.pure _ | exact StateStable.fault _

private theorem stable_expectArray (value : Val) : StateStable (expectArray value) :=
  fun _ _ _ success => expectArray_state success

private theorem stable_expectSameTy (left right : IntTy) : StateStable (expectSameTy left right) := by
  unfold expectSameTy
  split
  · exact StateStable.pure _
  · exact StateStable.fault _

private theorem stable_expectComparable (left right : Val) : StateStable (expectComparable left right) := by
  cases left <;> cases right <;> simp only [expectComparable]
  all_goals first
    | exact StateStable.pure _
    | exact StateStable.fault _
    | exact (stable_expectSameTy _ _).bind fun _ => StateStable.pure _

private theorem stable_expectArrayLit (type : Ty) (elements : Array Val) :
    StateStable (expectArrayLit type elements) := by
  cases type <;> simp only [expectArrayLit]
  all_goals first
    | exact StateStable.pure _
    | exact StateStable.fault _
    | (split <;> first | exact StateStable.pure _ | exact StateStable.fault _)

private theorem stable_expectFixedCount (type : Ty) : StateStable (expectFixedCount type) := by
  cases type <;> first | exact StateStable.pure _ | exact StateStable.fault _

private theorem stable_slotRoot (f : Func) (fr : Frame) (slot : SlotId) : StateStable (slotRoot f fr slot) := by
  unfold slotRoot
  split
  · exact StateStable.fault _
  · split
    · exact StateStable.fault _
    · exact StateStable.pure _

private theorem stable_mapList {get : α → M β} (stable : ∀ value, StateStable (get value)) :
    ∀ values, StateStable (mapList get values) := by
  intro values
  induction values with
  | nil => exact StateStable.pure _
  | cons value values ih =>
    exact (stable value).bind fun _ => ih.bind fun _ => StateStable.pure _

private theorem stable_evalBnd (fr : Frame) (len : Nat) (default : Int) (bound : Bnd) :
    StateStable (evalBnd fr len default bound) := by
  cases bound with
  | omitted => exact StateStable.pure _
  | val id | fromEnd id =>
    exact (stable_getVal fr id).bind fun value =>
      (stable_expectInt value).bind fun _ => StateStable.pure _

theorem execPure_state {cx : FnCtx} {fr : Frame} {op : Op} {result : ValueId}
    {state after : St} {cell : RVal} (preserved : killsLengths (.def result op) = false)
    (success : execPure cx fr op state = .ok cell after) : after = state := by
  have stable : StateStable (execPure cx fr op) := by
    cases op with
    | push | pop | call => simp [killsLengths] at preserved
    | constInt | constBool | constUnit | globalAddr => exact StateStable.pure _
    | slotAddr slot => exact (stable_slotRoot cx.fn fr slot).bind fun _ => StateStable.pure _
    | bin operator type left right origin =>
      exact (stable_getVal fr left).bind fun lv => (stable_expectInt lv).bind fun li =>
        (stable_getVal fr right).bind fun rv => (stable_expectInt rv).bind fun ri =>
        (stable_expectSameTy li.1 ri.1).bind fun _ => by
          split
          · exact StateStable.pure _
          · exact StateStable.abort _ _
    | un operator type value origin =>
      exact (stable_getVal fr value).bind fun v => (stable_expectInt v).bind fun vi => by
        rcases vi with ⟨operandType, number⟩
        dsimp only
        split
        · exact StateStable.pure _
        · exact StateStable.abort _ _
    | cmp operator type left right | boolCmp operator left right =>
      exact (stable_getVal fr left).bind fun lv => (stable_getVal fr right).bind fun rv =>
        (stable_expectComparable lv rv).bind fun _ => StateStable.pure _
    | boolNot id =>
      exact (stable_getVal fr id).bind fun value =>
        (stable_expectBool value).bind fun _ => StateStable.pure _
    | conv kind src dst id origin =>
      exact (stable_getVal fr id).bind fun value => (stable_expectInt value).bind fun vi => by
        rcases vi with ⟨operandType, number⟩
        dsimp only
        split
        · exact StateStable.pure _
        · exact StateStable.abort _ _
    | next type id =>
      exact (stable_getVal fr id).bind fun value =>
        (stable_expectInt value).bind fun _ => StateStable.pure _
    | refElem view index =>
      exact (stable_getView fr view).bind fun vw =>
        (stable_getVal fr index).bind fun value => (stable_expectInt value).bind fun vi => by
          rcases vi with ⟨operandType, number⟩
          dsimp only
          split
          · exact StateStable.pure _
          · exact StateStable.fault _
    | refFreeze reference =>
      exact (stable_getVal fr reference).bind fun value =>
        (stable_expectRef value).bind fun _ => StateStable.pure _
    | load reference =>
      exact (stable_getVal fr reference).bind fun value => (stable_expectRef value).bind fun loc =>
        (stable_readLoc loc).bind fun _ => StateStable.pure _
    | snapshot mode reference | arrayLen reference =>
      exact (stable_getVal fr reference).bind fun value => (stable_expectRef value).bind fun loc =>
        (stable_readLoc loc).bind fun array => (stable_expectArray array).bind fun _ => StateStable.pure _
    | sliceView id =>
      exact (stable_getVal fr id).bind fun value =>
        (stable_expectSlice value).bind fun _ => StateStable.pure _
    | viewLen id => exact (stable_getView fr id).bind fun _ => StateStable.pure _
    | viewSlice mutability view lo hi origin =>
      exact (stable_getView fr view).bind fun vw => (stable_evalBnd fr vw.len 0 lo).bind fun lower =>
        (stable_evalBnd fr vw.len vw.len hi).bind fun upper => by
          split
          · exact StateStable.pure _
          · exact StateStable.abort _ _
    | indexChecked view index origin =>
      exact (stable_getView fr view).bind fun vw => (stable_getVal fr index).bind fun value =>
        (stable_expectInt value).bind fun vi => by
          rcases vi with ⟨operandType, number⟩
          dsimp only
          split
          · exact StateStable.pure _
          · exact StateStable.abort _ _
    | indexProven view index =>
      exact (stable_getView fr view).bind fun vw => (stable_getVal fr index).bind fun value =>
        (stable_expectInt value).bind fun _ => StateStable.pure _
    | arrLit type values =>
      exact (stable_mapList (stable_getVal fr) values).bind fun array =>
        (stable_expectArrayLit type array.toArray).bind fun _ => StateStable.pure _
    | arrFill type id =>
      exact (stable_expectFixedCount type).bind fun _ =>
        (stable_getVal fr id).bind fun _ => StateStable.pure _
    | structLit type values =>
      simp only [execPure]
      split
      · exact (stable_mapList (stable_getVal fr) values).bind fun _ => StateStable.pure _
      · exact StateStable.fault _
    | fieldAddr owner field =>
      exact (stable_getVal fr owner).bind fun value =>
        (stable_expectRef value).bind fun _ => StateStable.pure _
  exact stable state cell after success

theorem execOp_state {fuel : Nat} {cx : FnCtx} {fr : Frame} {op : Op} {result : ValueId}
    {state after : St} {cell : RVal} (preserved : killsLengths (.def result op) = false)
    (success : execOp fuel cx fr op state = .ok cell after) : after = state := by
  have pureSuccess : execPure cx fr op state = .ok cell after := by
    cases op <;> first
      | simpa only [execOp] using success
      | simp [killsLengths] at preserved
  exact execPure_state preserved pureSuccess

theorem FactsHold.defKills {fuel : Nat} {cx : FnCtx} {fr : Frame} {op : Op} {result : ValueId}
    {state after : St} {cell : RVal} {facts : Facts} (hold : FactsHold fr state facts)
    (success : execOp fuel cx fr op state = .ok cell after) :
    FactsHold (withCell fr result cell) after
      (if killsLengths (.def result op) then
        Goose.GIR.killLengths (Goose.GIR.killValue facts result)
      else Goose.GIR.killValue facts result) := by
  cases mutates : killsLengths (.def result op) with
  | true => exact FactsHold.mutatingDef hold result cell
  | false =>
    have same := execOp_state mutates success
    subst after
    exact FactsHold.killValue hold result cell

private theorem snapshotFold_sound {fr : Frame} {state : St} {source : Facts}
    {reference result : ValueId}
    (generated : ∀ found bound, .lenGe found bound ∈ source → found = reference →
      FactHolds fr state (.viewLenGe result bound)) :
    ∀ {initial : Facts}, FactsHold fr state initial →
      FactsHold fr state (source.foldl (fun acc fact => match fact with
        | .lenGe found bound => if found == reference then addFact acc (.viewLenGe result bound) else acc
        | _ => acc) initial) := by
  induction source with
  | nil => intro initial hold; exact hold
  | cons fact source ih =>
    intro initial hold
    apply ih (fun found bound member => generated found bound (by simp [member]))
    cases fact with
    | ge0 | lt | viewLenGe => exact hold
    | lenGe found bound =>
      by_cases same : found = reference
      · simp only [same, beq_self_eq_true, ↓reduceIte]
        exact FactsHold.add hold (generated found bound (by simp) same)
      · simpa [beq_eq_false_iff_ne.mpr same] using hold

theorem transfer_def_sound {fuel : Nat} {cx : FnCtx} {fr : Frame} {op : Op} {result : ValueId}
    {state after : St} {cell : RVal} {facts outgoing : Facts}
    (hold : FactsHold fr state facts)
    (freshLength : ∀ reference, op = .arrayLen reference → result ≠ reference)
    (success : execOp fuel cx fr op state = .ok cell after)
    (checked : transferInst cx.cfg.mod cx.fn facts (.def result op) = .ok outgoing) :
    FactsHold (withCell fr result cell) after outgoing := by
  have survives := FactsHold.defKills (result := result) hold success
  cases op with
  | constInt type number =>
    cases type <;> simp [transferInst, killsLengths, pure, Except.pure] at checked
    all_goals first
      | (subst outgoing; exact survives)
      | (split at checked
         · subst outgoing
           exact FactsHold.add survives (constInt_fact (by assumption) (by simpa [execOp] using success))
         · subst outgoing
           exact survives)
  | arrayLen reference =>
    simp [transferInst, killsLengths, pure, Except.pure] at checked
    subst outgoing
    obtain ⟨nonnegative, length⟩ := arrayLen_facts (freshLength reference rfl)
      (by simpa [execOp] using success)
    exact FactsHold.add (FactsHold.add survives length) nonnegative
  | snapshot mode reference =>
    simp only [transferInst, killsLengths, Bool.false_eq_true, ↓reduceIte,
      pure, Except.pure, Except.ok.injEq] at checked
    subst outgoing
    have generated : ∀ found bound, .lenGe found bound ∈ Goose.GIR.killValue facts result →
        found = reference → FactHolds (withCell fr result cell) after (.viewLenGe result bound) := by
      intro found bound member same
      subst found
      obtain ⟨original, kept⟩ := List.mem_filter.mp member
      have fresh : result ≠ bound := by
        intro same
        subst bound
        simp [Fact.mentions] at kept
      exact snapshot_fact fresh (hold (.lenGe reference bound) original)
        (by simpa [execOp] using success)
    have combined := snapshotFold_sound (source := Goose.GIR.killValue facts result)
      (initial := Goose.GIR.killValue facts result) generated survives
    exact combined
  | indexProven view index =>
    by_cases justified : provesIndex facts view index = true
    · simp [transferInst, justified, killsLengths, pure, Except.pure] at checked
      subst outgoing
      exact survives
    · have unjustified : provesIndex facts view index = false := Bool.eq_false_iff.mpr justified
      simp [transferInst, unjustified, bind, Except.bind] at checked
  | _ =>
    simp [transferInst, pure, Except.pure] at checked
    subst outgoing
    exact survives

theorem ArrayLenAt.sameStore {state after : St} {loc : Loc} {len : Nat}
    (stores : after.store = state.store) (hold : ArrayLenAt state loc len) :
    ArrayLenAt after loc len := by
  obtain ⟨array, resizable, read, length⟩ := hold
  have stored : state.store.read loc = .ok array := by
    unfold readLoc at read
    cases found : state.store.read loc with
    | error kind => simp [found] at read
    | ok value =>
      simp only [found, Res.ok.injEq] at read
      simp [← read.1]
  refine ⟨array, resizable, by simp [readLoc, stores, stored], ?_⟩
  cases array <;> simp [expectArray, pure, M.pure', fault, M.stop] at length ⊢
  all_goals exact length

theorem FactHolds.sameStore {fr next : Frame} {state after : St} {fact : Fact}
    (cells : next.vals = fr.vals) (stores : after.store = state.store)
    (hold : FactHolds fr state fact) : FactHolds next after fact := by
  cases fact with
  | ge0 i => simpa [FactHolds, IntAt, cells] using hold
  | lt i n => simpa [FactHolds, IntAt, cells] using hold
  | viewLenGe v n => simpa [FactHolds, ViewAt, IntAt, cells] using hold
  | lenGe r n =>
    obtain ⟨loc, bound, len, ref, atBound, length, less⟩ := hold
    exact ⟨loc, bound, len, by simpa [RefAt, cells] using ref,
      by simpa [IntAt, cells] using atBound, ArrayLenAt.sameStore stores length, less⟩

private theorem stable_render (value : Val) : StateStable (render value) := by
  cases value with
  | bool bit => cases bit <;> exact StateStable.pure _
  | int => exact StateStable.pure _
  | _ => exact StateStable.fault _

private theorem stable_renderPart (fr : Frame) (part : PrintPart) : StateStable (renderPart fr part) := by
  cases part with
  | text text => exact StateStable.pure _
  | val id => exact (stable_getVal fr id).bind fun value => stable_render value

theorem execEff_print_store {f : Func} {fr next : Frame} {parts : List PrintPart}
    {origin : Option OriginId} {state after : St}
    (success : execEff f fr (.print parts origin) state = .ok next after) :
    after.store = state.store := by
  simp only [execEff] at success
  obtain ⟨strings, first, evaluated, success⟩ := success_bind success
  obtain ⟨ignored, second, emitted, success⟩ := success_bind success
  have same := stable_mapList (stable_renderPart fr) parts state strings first evaluated
  subst first
  simp only [emit, Res.ok.injEq] at emitted
  have sameSecond := emitted.2
  subst second
  simp only [pure_apply, Res.ok.injEq] at success
  have storeSame := congrArg St.store success.2.symm
  exact storeSame

theorem transfer_effect_sound {cx : FnCtx} {fr next : Frame} {effect : Effect}
    {state after : St} {facts outgoing : Facts} (hold : FactsHold fr state facts)
    (success : execEff cx.fn fr effect state = .ok next after)
    (checked : transferInst cx.cfg.mod cx.fn facts (.eff effect) = .ok outgoing) :
    FactsHold next after outgoing := by
  cases effect with
  | print parts origin =>
    simp [transferInst, killsLengths, pure, Except.pure] at checked
    subst outgoing
    intro fact member
    exact FactHolds.sameStore (execEff_cells success) (execEff_print_store success) (hold fact member)
  | _ =>
    simp [transferInst, killsLengths, pure, Except.pure] at checked
    subst outgoing
    exact FactsHold.mutatingEffect hold success

private theorem refTy_cell {env : TyEnv} {reference : ValueId} {mutability : Mutability} {owner : Ty}
    (typed : env.refTy reference = .ok (mutability, owner)) :
    env.vals[reference]? = some (some (.data (.ref mutability owner))) := by
  unfold TyEnv.refTy at typed
  obtain ⟨type, dataType, typed⟩ := Goose.GIR.bind_ok typed
  cases type with
  | ref mutability owner =>
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at typed
    obtain ⟨rfl, rfl⟩ := typed
    exact Goose.GIR.dataTy_of dataType
  | _ => simp [tyErr] at typed

theorem typed_arrayLen_fresh {env : TyEnv} {result reference : ValueId} {type : VTy}
    (typed : Op.resultTy env (.arrayLen reference) = .ok type)
    (defined : env.vals[result]? = some (some type)) : result ≠ reference := by
  intro same
  subst result
  simp only [Op.resultTy] at typed
  obtain ⟨pair, refType, typed⟩ := Goose.GIR.bind_ok typed
  rcases pair with ⟨mutability, owner⟩
  have referenceType := refTy_cell refType
  split at typed
  · simp only [pure, Except.pure, Except.ok.injEq] at typed
    subst type
    rw [defined] at referenceType
    simp at referenceType
  · simp [tyErr] at typed

theorem validated_arrayLen_fresh {m : GIR.Module} {f : Func} {block : GIR.Block}
    {result reference : ValueId} (validated : validate m = .ok ())
    (functionMember : f ∈ m.allFuncs) (blockMember : block ∈ f.blocks)
    (instructionMember : .def result (.arrayLen reference) ∈ block.insts) : result ≠ reference := by
  obtain ⟨_, typed, _⟩ := (Goose.GIR.validate_sound m validated).1 f functionMember
  obtain ⟨type, resultType, valueType⟩ := typed block blockMember result (.arrayLen reference) instructionMember
  exact typed_arrayLen_fresh resultType valueType

end Goose.Proofs.Bounds
