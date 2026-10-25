import Goose.Lower.Validation.CfgGeneratedEdgeActions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem generated_edge_intTyOf (env : LEnv) (context : Option LoopCtx) (value : ValueId) :
    GeneratedEdgeRun env context (intTyOf value) := by
  apply GeneratedEdgeRun.of_edgeRun (edge_intTyOf value)
  intro before result after run generated _
  exact generated.intTyOf value run

theorem generated_edge_freezeTo (env : LEnv) (context : Option LoopCtx) (mu : Mutability) (value : ValueId) :
    GeneratedEdgeRun env context (freezeTo mu value) := by
  apply GeneratedEdgeRun.of_edgeRun (edge_freezeTo mu value)
  intro before result after run generated _
  exact generated.freezeTo mu value run

theorem generated_edge_borrowTo (env : LEnv) (context : Option LoopCtx) (mu : Mutability) (value : ValueId) :
    GeneratedEdgeRun env context (borrowTo mu value) := by
  apply GeneratedEdgeRun.of_edgeRun (edge_borrowTo mu value)
  intro before result after run generated _
  exact generated.borrowTo mu value run

theorem generated_edge_coerceTo (env : LEnv) (context : Option LoopCtx) (ty : Ty) (value : ValueId) (origin : OriginId) :
    GeneratedEdgeRun env context (coerceTo ty value origin) := by
  apply GeneratedEdgeRun.of_edgeRun (edge_coerceTo ty value origin)
  intro before result after run generated _
  exact generated.coerceTo ty value origin run

theorem generated_edge_coerceSlot (env : LEnv) (context : Option LoopCtx) (slot : SlotId) (value : ValueId) (origin : OriginId) :
    GeneratedEdgeRun env context (coerceSlot slot value origin) := by
  apply GeneratedEdgeRun.of_edgeRun (edge_coerceSlot slot value origin)
  intro before result after run generated _
  exact generated.coerceSlot slot value origin run

theorem generated_edge_coerceResult (env : LEnv) (context : Option LoopCtx) (value : ValueId) (origin : OriginId) :
    GeneratedEdgeRun env context (coerceResult value origin) := by
  apply GeneratedEdgeRun.of_edgeRun (edge_coerceResult value origin)
  intro before result after run generated _
  exact generated.coerceResult value origin run

theorem generated_edge_initSlots (env : LEnv) (context : Option LoopCtx) (slots : List (SlotId × ValueId × OriginId)) :
    GeneratedEdgeRun env context (initSlots slots) := by
  apply GeneratedEdgeRun.of_edgeRun (edge_initSlots slots)
  intro before result after run generated _
  exact generated.initSlots slots run

theorem generated_edge_leaveTo (env : LEnv) (context : Option LoopCtx) (depth : Nat) :
    GeneratedEdgeRun env context (leaveTo depth) := by
  apply GeneratedEdgeRun.of_edgeRun (edge_leaveTo depth)
  intro before result after run generated _
  exact generated.leaveTo depth run

theorem generated_edge_regrowOf (env : LEnv) (context : Option LoopCtx) (owner : Option ValueId) :
    GeneratedEdgeRun env context (regrowOf owner) := by
  apply GeneratedEdgeRun.of_edgeRun (edge_regrowOf owner)
  intro before result after run generated _
  exact generated.regrowOf owner run

theorem generated_edge_eachSampled (env : LEnv) (context : Option LoopCtx) (regrow : Bool) (view : ValueId) :
    GeneratedEdgeRun env context (eachSampled regrow view) := by
  apply GeneratedEdgeRun.of_edgeRun (edge_eachSampled regrow view)
  intro before result after run generated _
  exact generated.eachSampled regrow view run

theorem generated_edge_eachLen (env : LEnv) (context : Option LoopCtx) (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    GeneratedEdgeRun env context (eachLen regrow owner sampled) := by
  apply GeneratedEdgeRun.of_edgeRun (edge_eachLen regrow owner sampled)
  intro before result after run generated _
  exact generated.eachLen regrow owner sampled run

theorem generated_edge_eachElemValue (env : LEnv) (context : Option LoopCtx) (slot : VarId) (byRef : Bool) (value : ValueId) :
    GeneratedEdgeRun env context (eachElemValue slot byRef value) := by
  apply GeneratedEdgeRun.of_edgeRun (edge_eachElemValue slot byRef value)
  intro before result after run generated _
  exact generated.eachElemValue slot byRef value run

theorem generated_edge_pushScope (env : LEnv) (context : Option LoopCtx) (scope : ScopeId) :
    GeneratedEdgeRun env context (pushScope scope) := by
  apply GeneratedEdgeRun.of_edgeRun (EdgeRun.of_tables (by intros; rw [pushScope_run]; exact ⟨rfl, rfl⟩))
  intro before result after run generated _
  rw [pushScope_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨generated.dense, generated.live, generated.targets⟩

theorem generated_edge_popScope (env : LEnv) (context : Option LoopCtx) :
    GeneratedEdgeRun env context popScope := by
  apply GeneratedEdgeRun.of_edgeRun (EdgeRun.of_tables (by intros; rw [popScope_run]; exact ⟨rfl, rfl⟩))
  intro before result after run generated _
  rw [popScope_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨generated.dense, generated.live, generated.targets⟩

theorem generated_edge_inScope (env : LEnv) (context : Option LoopCtx) (scope : ScopeId) {body : B α}
    (bodyEdges : GeneratedEdgeRun env context body) : GeneratedEdgeRun env context (inScope scope body) := by
  unfold inScope
  exact (generated_edge_pushScope env context scope).bind fun _ => bodyEdges.bind fun value =>
    (generated_edge_popScope env context).bind fun _ => generated_edge_pure env context value

theorem generated_edge_emitTerm (env : LEnv) (context : Option LoopCtx) (term : Term)
    (typed : ∀ state, BuilderTermArguments state term) : GeneratedEdgeRun env context (emitTerm term) := by
  intro before result after run generated loop checked
  exact generated_edge_emitTerm_at term env before after result run generated checked (typed before)

theorem generated_edge_whenLive (env : LEnv) (context : Option LoopCtx) (default : α) {body : BlockId → B α}
    (children : ∀ block, GeneratedEdgeRun env context (body block)) :
    GeneratedEdgeRun env context (whenLive default body) := by
  intro before result after run generated loop checked
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨generated, .refl before, checked⟩
  | some block =>
    rw [whenLive_some _ _ env current] at run
    exact children block before result after run generated loop checked

end Goose.Lower.Validation
