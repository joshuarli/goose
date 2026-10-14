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

end Goose.Proofs.Bounds
