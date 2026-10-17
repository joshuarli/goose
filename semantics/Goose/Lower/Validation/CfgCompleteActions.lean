import Goose.Lower.Validation.CfgCompleteIf

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem complete_valTy (value : ValueId) : CompletionAction (valTy value) :=
  CompletionAction.of_state (open_valTy value)
    (fun env state => by rw [valTy_run]) (fun env state => by rw [valTy_run])

theorem complete_intTyOf (value : ValueId) : CompletionAction (intTyOf value) :=
  CompletionAction.of_state (open_intTyOf value)
    (fun env state => congrArg LS.blocks (intTyOf_eq (v := value) (le := env) (ls := state) rfl))
    (fun env state => congrArg LS.cur (intTyOf_eq (v := value) (le := env) (ls := state) rfl))

theorem complete_recordReadValueRootRecipe (value : ValueId) (place : Place) :
    CompletionAction (recordReadValueRootRecipe value place) :=
  CompletionAction.of_state (open_recordReadValueRootRecipe value place)
    (fun env state => (recordReadValueRootRecipe_tables value place env state).1)
    (fun env state => (recordReadValueRootRecipe_tables value place env state).2.2)

theorem complete_read : CompletionAction (read : B LEnv) :=
  CompletionAction.of_state open_read (fun _ _ => rfl) (fun _ _ => rfl)

theorem complete_get : CompletionAction (get : B LS) :=
  CompletionAction.of_state open_get (fun _ _ => rfl) (fun _ _ => rfl)

theorem complete_isLive : CompletionAction isLive :=
  CompletionAction.of_state open_isLive (fun _ _ => rfl) (fun _ _ => rfl)

theorem complete_freezeTo (mu : Mutability) (value : ValueId) : CompletionAction (freezeTo mu value) := by
  refine ⟨open_freezeTo mu value, ?_⟩
  intro env before result after run openBefore shapedBefore
  rcases freezeTo_cases run with ⟨_, same⟩ | emitted
  · exact ⟨shapedBefore.of_blocks (by rw [same]), by simp [same]⟩
  · exact (complete_emitDef _).complete env before result after emitted openBefore shapedBefore

theorem complete_borrowTo (mu : Mutability) (value : ValueId) : CompletionAction (borrowTo mu value) := by
  refine ⟨open_borrowTo mu value, ?_⟩
  intro env before result after run openBefore shapedBefore
  rcases borrowTo_cases run with frozen | emitted
  · exact (complete_freezeTo mu value).complete env before result after frozen openBefore shapedBefore
  · exact (complete_emitDef _).complete env before result after emitted openBefore shapedBefore

theorem complete_coerceTo (target : Ty) (value : ValueId) (origin : OriginId) :
    CompletionAction (coerceTo target value origin) := by
  refine ⟨open_coerceTo target value origin, ?_⟩
  intro env before result after run openBefore shapedBefore
  rcases coerceTo_cases run with ⟨_, same⟩ | ⟨elem, _, emitted⟩ | ⟨elem, view, middle, _, first, second⟩
  · exact ⟨shapedBefore.of_blocks (by rw [same]), by simp [same]⟩
  · exact (complete_emitDef _).complete env before result after emitted openBefore shapedBefore
  · obtain ⟨shapeMiddle, countFirst⟩ := (complete_emitDef _).complete env before view middle first openBefore shapedBefore
    have openMiddle := (open_emitDef _).paths env before view middle first openBefore openBefore.bound
    obtain ⟨shapeAfter, countSecond⟩ := (complete_emitDef _).complete env middle result after second openMiddle shapeMiddle
    exact ⟨shapeAfter, by omega⟩

theorem complete_inScope (scope : ScopeId) {action : B α} (child : CompletionAction action) :
    CompletionAction (inScope scope action) := by
  refine ⟨open_inScope scope child.openAction, ?_⟩
  intro env before result after run openBefore shapedBefore
  obtain ⟨middle, childRun, same⟩ := inScope_eq run
  have openStarted : CurrentOpen { before with stack := scope :: before.stack } := openBefore.of_state rfl rfl
  have shapeStarted : ShapedBlocks { before with stack := scope :: before.stack } := shapedBefore.of_blocks rfl
  obtain ⟨shapeMiddle, countMiddle⟩ := child.complete env _ result middle childRun openStarted shapeStarted
  refine ⟨shapeMiddle.of_blocks (by rw [same]), ?_⟩
  simpa only [same, OpenCount, LiveCount] using countMiddle

theorem complete_coerceSlot (slot : SlotId) (value : ValueId) (origin : OriginId) :
    CompletionAction (coerceSlot slot value origin) := by
  unfold coerceSlot
  refine CompletionAction.bind complete_read fun env => ?_
  cases env.slots[slot]? with
  | none => exact CompletionAction.pure _
  | some destination => exact complete_coerceTo _ _ _

theorem complete_coerceResult (value : ValueId) (origin : OriginId) :
    CompletionAction (coerceResult value origin) := by
  unfold coerceResult
  refine CompletionAction.bind complete_read fun env => ?_
  cases env.results.head? with
  | none => exact CompletionAction.pure _
  | some destination => exact complete_coerceTo _ _ _

theorem complete_growOwner (value : ValueId) : CompletionAction (growOwner value) := by
  unfold growOwner
  refine CompletionAction.bind (complete_valTy value) fun ty => ?_
  cases ty with
  | data ty => cases ty <;> exact CompletionAction.pure _
  | view _ _ => exact CompletionAction.pure _

theorem complete_initSlots : ∀ pre, CompletionAction (initSlots pre)
  | [] => CompletionAction.pure _
  | _ :: rest => CompletionAction.bind (complete_emitEffect _) fun _ => complete_initSlots rest

theorem complete_leaveAll : ∀ scopes, CompletionAction (leaveAll scopes)
  | [] => CompletionAction.pure _
  | _ :: rest => CompletionAction.bind (complete_emitEffect _) fun _ => complete_leaveAll rest

theorem complete_leaveTo (depth : Nat) : CompletionAction (leaveTo depth) := by
  unfold leaveTo
  exact CompletionAction.bind complete_get fun _ => complete_leaveAll _

theorem complete_regrowOf (owner : Option ValueId) : CompletionAction (regrowOf owner) := by
  cases owner with
  | none => exact CompletionAction.pure _
  | some value => exact complete_growOwner value

theorem complete_eachSampled (regrow : Bool) (view : ValueId) : CompletionAction (eachSampled regrow view) := by
  unfold eachSampled
  cases regrow
  · exact complete_emitDef _
  · exact CompletionAction.pure _

theorem complete_eachElemValue (var : VarId) (byRef : Bool) (elem : ValueId) :
    CompletionAction (eachElemValue var byRef elem) := by
  unfold eachElemValue
  cases byRef
  · exact complete_emitDef _
  · refine CompletionAction.bind complete_read fun env => ?_
    cases env.vars[var]? with
    | none => exact CompletionAction.pure _
    | some localVar =>
      dsimp only
      cases localVar.ty <;> first | exact CompletionAction.pure _ | exact complete_borrowTo _ _

theorem CompletionAction.advance {action : B α} (child : CompletionAction action) : AdvB action :=
  child.openAction.advance

theorem CompletionAction.live {action : B α} (child : CompletionAction action) : LiveCompletionRun action :=
  fun env before result after run openBefore shapedBefore _ =>
    child.complete env before result after run openBefore shapedBefore

theorem complete_whenLive (default : α) {action : B α}
    (openAction : OpenAction (whenLive default fun _ => action)) (child : LiveCompletionRun action) :
    CompletionAction (whenLive default fun _ => action) := by
  refine ⟨openAction, ?_⟩
  intro env before result after run openBefore shapedBefore
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨shapedBefore, rfl⟩
  | some block =>
    rw [whenLive_some _ _ env current] at run
    exact child env before result after run openBefore shapedBefore (by simp [current])

end Goose.Lower.Validation
