import Goose.Lower.Validation.CfgReadRecipes
import Goose.Lower.Validation.CfgEdgeLoops
import Goose.Lower.GeneratedBuilder

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem EdgeArguments.bound {state : LS} {target : BlockId} {args : List ValueId}
    (edge : EdgeArguments state target args) : target < state.blocks.size := by
  obtain ⟨body, row, _, _⟩ := edge
  exact (Array.getElem?_eq_some_iff.mp row).1

theorem CounterHeader.bound {state : LS} {header : BlockId} {ty : IntTy} {counter : ValueId}
    (frame : CounterHeader state header ty counter) : header < state.blocks.size := by
  obtain ⟨body, row, _⟩ := frame
  exact (Array.getElem?_eq_some_iff.mp row).1

theorem LoopEdgeArguments.targets {context : Option LoopCtx} {state : LS}
    (loop : LoopEdgeArguments context state) : LoopBuilderTargets context state := by
  cases context with
  | none => trivial
  | some context =>
    refine ⟨loop.1.bound, ?_⟩
    cases kind : context.cont with
    | jump header =>
      have edge : EdgeArguments state header [] := by simpa [kind] using loop.2
      exact edge.bound
    | next header ty counter =>
      have frame : CounterHeader state header ty counter ∧ state.vals[counter]? = some (some (.data (.int ty))) := by
        simpa [kind] using loop.2
      exact frame.1.bound

theorem BuilderTermArguments.targetBound {state : LS} {term : Term}
    (arguments : BuilderTermArguments state term) : ∀ target ∈ term.successors, target < state.blocks.size := by
  cases term <;> simp only [Term.successors, List.mem_cons, List.not_mem_nil, or_false] <;> try (intro target member; contradiction)
  case br destination args =>
    intro target same
    subst target
    exact arguments.bound
  case condbr condition yes yesArgs no noArgs =>
    intro target member
    rcases member with rfl | rfl
    · exact arguments.1.bound
    · exact arguments.2.bound

def GeneratedEdgeRun (env : LEnv) (context : Option LoopCtx) (action : B α) : Prop :=
  ∀ before result after, action env before = (result, after) →
    GeneratedBuilderState before → LoopEdgeArguments context before → BuilderEdgeArguments before →
      GeneratedBuilderState after ∧ EdgeExtension before after ∧ BuilderEdgeArguments after

theorem GeneratedEdgeRun.bind {env : LEnv} {context : Option LoopCtx} {first : B α} {next : α → B β}
    (one : GeneratedEdgeRun env context first) (two : ∀ value, GeneratedEdgeRun env context (next value)) :
    GeneratedEdgeRun env context (first >>= next) := by
  intro before result after run generated loop checked
  obtain ⟨value, middle, firstRun, nextRun⟩ := bind_eq.mp run
  obtain ⟨middleGenerated, middleExtension, middleChecked⟩ := one before value middle firstRun generated loop checked
  obtain ⟨afterGenerated, afterExtension, afterChecked⟩ := two value middle result after nextRun middleGenerated
    (loop.extend middleExtension) middleChecked
  exact ⟨afterGenerated, middleExtension.trans afterExtension, afterChecked⟩

theorem GeneratedEdgeRun.of_edgeRun {env : LEnv} {context : Option LoopCtx} {action : B α}
    (edges : EdgeRun action)
    (ready : ∀ before result after, action env before = (result, after) →
      GeneratedBuilderState before → LoopEdgeArguments context before → GeneratedBuilderState after) :
    GeneratedEdgeRun env context action := by
  intro before result after run generated loop checked
  obtain ⟨extension, afterChecked⟩ := edges env before result after run checked
  exact ⟨ready before result after run generated loop, extension, afterChecked⟩

theorem GeneratedEdgeRun.unchanged {env : LEnv} {context : Option LoopCtx} {action : B α}
    (same : ∀ state, (action env state).2 = state) : GeneratedEdgeRun env context action := by
  intro before result after run generated loop checked
  have equal := same before
  rw [run] at equal
  change after = before at equal
  subst after
  exact ⟨generated, .refl before, checked⟩

theorem GeneratedEdgeRun.withLoop {env : LEnv} {action : B α}
    (run : GeneratedEdgeRun env none action) (context : Option LoopCtx) : GeneratedEdgeRun env context action :=
  fun before result after lowered generated _ checked => run before result after lowered generated trivial checked

theorem generated_edge_pure (env : LEnv) (context : Option LoopCtx) (value : α) :
    GeneratedEdgeRun env context (pure value) := GeneratedEdgeRun.unchanged (by intros; rfl)

theorem generated_edge_read (env : LEnv) (context : Option LoopCtx) :
    GeneratedEdgeRun env context (read : B LEnv) := GeneratedEdgeRun.unchanged (by intros; rfl)

theorem generated_edge_get (env : LEnv) (context : Option LoopCtx) :
    GeneratedEdgeRun env context (get : B LS) := GeneratedEdgeRun.unchanged (by intros; rfl)

theorem generated_edge_valTy (env : LEnv) (context : Option LoopCtx) (value : ValueId) :
    GeneratedEdgeRun env context (valTy value) := GeneratedEdgeRun.unchanged (valTy_run value env)

theorem generated_edge_isLive (env : LEnv) (context : Option LoopCtx) :
    GeneratedEdgeRun env context isLive := GeneratedEdgeRun.unchanged (by intros; rfl)

theorem generated_edge_curBlock (env : LEnv) (context : Option LoopCtx) :
    GeneratedEdgeRun env context curBlock := GeneratedEdgeRun.unchanged (by intros; rw [curBlock_run])

theorem generated_edge_recordReadValueRootRecipe (env : LEnv) (context : Option LoopCtx)
    (value : ValueId) (place : Place) :
    GeneratedEdgeRun env context (recordReadValueRootRecipe value place) := by
  apply GeneratedEdgeRun.of_edgeRun (EdgeRun.of_tables (fun env state =>
    ⟨(recordReadValueRootRecipe_tables value place env state).1,
      (recordReadValueRootRecipe_tables value place env state).2.1⟩))
  intro before result after run generated loop
  exact generated.of_runs (dense_recordReadValueRootRecipe value place)
    (generatedTargets_recordReadValueRootRecipe context value place) loop.targets run

theorem generated_edge_emitDef (env : LEnv) (context : Option LoopCtx) (op : Op) :
    GeneratedEdgeRun env context (emitDef op) := by
  apply GeneratedEdgeRun.of_edgeRun (edge_emitDef op)
  intro before result after run generated _
  exact generated.emitDef op run

theorem generated_edge_emitEffect (env : LEnv) (context : Option LoopCtx) (effect : Effect) :
    GeneratedEdgeRun env context (emitEffect effect) := by
  apply GeneratedEdgeRun.of_edgeRun (edge_emitEffect effect)
  intro before result after run generated _
  exact generated.emitEffect effect run

theorem generated_edge_newBlock0 (env : LEnv) (context : Option LoopCtx) :
    GeneratedEdgeRun env context (newBlock []) := by
  apply GeneratedEdgeRun.of_edgeRun edge_newBlock0
  intro before result after run generated _
  exact generated.newBlock [] run

theorem generated_edge_newBlock1 (env : LEnv) (context : Option LoopCtx) (ty : VTy) :
    GeneratedEdgeRun env context (newBlock [ty]) := by
  apply GeneratedEdgeRun.of_edgeRun (edge_newBlock1 ty)
  intro before result after run generated _
  exact generated.newBlock [ty] run

theorem generated_edge_emitTerm_at (term : Term) (env : LEnv) (before after : LS) (result : Unit)
    (run : emitTerm term env before = (result, after)) (generated : GeneratedBuilderState before)
    (checked : BuilderEdgeArguments before) (typed : BuilderTermArguments before term) :
    GeneratedBuilderState after ∧ EdgeExtension before after ∧ BuilderEdgeArguments after := by
  obtain ⟨extension, afterChecked⟩ := edge_emitTerm_at term env before after result run checked (fun _ => typed)
  exact ⟨generated.emitTerm term typed.targetBound run, extension, afterChecked⟩

theorem generated_edge_setCur_at (current : Option BlockId) (env : LEnv) (before after : LS) (result : Unit)
    (run : setCur current env before = (result, after)) (generated : GeneratedBuilderState before)
    (checked : BuilderEdgeArguments before) (bound : ∀ block, current = some block → block < before.blocks.size) :
    GeneratedBuilderState after ∧ EdgeExtension before after ∧ BuilderEdgeArguments after := by
  obtain ⟨extension, afterChecked⟩ := edge_setCur current env before result after run checked
  exact ⟨generated.setCur current bound run, extension, afterChecked⟩

theorem generated_edge_fork (env : LEnv) (context : Option LoopCtx) (condition : ValueId) :
    GeneratedEdgeRun env context (fork condition) := by
  apply GeneratedEdgeRun.of_edgeRun (edge_fork condition)
  intro before result after run generated _
  exact generated.fork condition run

theorem generated_edge_joinArms (env : LEnv) (context : Option LoopCtx) (yes no : Option BlockId) :
    GeneratedEdgeRun env context (joinArms yes no) := by
  apply GeneratedEdgeRun.of_edgeRun (edge_joinArms yes no)
  intro before result after run generated _
  exact generated.joinArms yes no run

end Goose.Lower.Validation
