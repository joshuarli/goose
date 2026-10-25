import Goose.Lower.Validation.CfgJoinPaths
import Goose.Lower.Validation.CfgFrontier

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem paths_emitDef (op : Op) : BoundedRun ReachableBuilder (emitDef op) := by
  intro env before result after run paths _
  have preserved := paths.emitDef op env
  rw [run] at preserved
  exact preserved

theorem paths_emitEffect (effect : Effect) : BoundedRun ReachableBuilder (emitEffect effect) := by
  intro env before result after run paths _
  have preserved := paths.emitEffect effect env
  rw [run] at preserved
  exact preserved

theorem paths_emitTerm (term : Term) : BoundedRun ReachableBuilder (emitTerm term) := by
  intro env before result after run paths _
  have preserved := paths.emitTerm term env
  rw [run] at preserved
  exact preserved

theorem paths_of_blocks_unchanged {action : B α}
    (blocks : ∀ env state, (action env state).2.blocks = state.blocks) :
    BoundedRun ReachableBuilder action := by
  intro env before result after run paths _
  apply paths.of_blocks
  have same := blocks env before
  simpa only [run] using same

theorem paths_valTy (value : ValueId) : BoundedRun ReachableBuilder (valTy value) :=
  paths_of_blocks_unchanged fun env state => by rw [valTy_run]

theorem paths_intTyOf (value : ValueId) : BoundedRun ReachableBuilder (intTyOf value) :=
  paths_of_blocks_unchanged fun env state =>
    congrArg LS.blocks (intTyOf_eq (v := value) (le := env) (ls := state) rfl)

theorem paths_read : BoundedRun ReachableBuilder (read : B LEnv) :=
  paths_of_blocks_unchanged fun _ _ => rfl

theorem paths_whenLive (default : α) (action : BlockId → B α)
    (preserves : ∀ block, BoundedRun ReachableBuilder (action block)) :
    BoundedRun ReachableBuilder (whenLive default action) := by
  intro env before result after run paths bounded
  cases current : before.cur with
  | none =>
    rw [whenLive_none default action env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact paths
  | some block =>
    rw [whenLive_some default action env current] at run
    exact preserves block env before result after run paths bounded

theorem paths_shortCircuit (isAnd : Bool) (value : ValueId) {rhs : B ValueId}
    (child : BoundedRun ReachableBuilder rhs) :
    BoundedRun ReachableBuilder (shortCircuit isAnd value rhs) := by
  intro env before result after run paths bounded
  cases current : before.cur with
  | none =>
    rw [shortCircuit, whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact paths
  | some block =>
    rw [shortCircuit, whenLive_some _ _ env current] at run
    obtain ⟨pair, forked, forkRun, run⟩ := bind_eq.mp run
    obtain ⟨_, started, startRun, run⟩ := bind_eq.mp run
    obtain ⟨_, childAfter, childRun, run⟩ := bind_eq.mp run
    obtain ⟨_, closed, closeRun, run⟩ := bind_eq.mp run
    obtain ⟨_, joined, joinRun, run⟩ := bind_eq.mp run
    obtain ⟨_, stateEqual⟩ := pure_eq.mp run
    have forkPaths := paths.scFork current (bounded block current) isAnd value env
    have forkBounds := liveBound_scFork current isAnd value env
    rw [forkRun] at forkPaths forkBounds
    dsimp only at forkPaths forkBounds
    have startedPaths := forkPaths.of_blocks (setCur_blocks startRun)
    have startedBound := liveBound_setCur forkBounds.1 env
    rw [startRun] at startedBound
    have childPaths := child env started _ childAfter childRun startedPaths startedBound
    have closedPaths := childPaths.emitTerm (.br pair.2.1 [((rhs env started).1)]) env
    rw [childRun] at closedPaths
    rw [closeRun] at closedPaths
    have joinedPaths := closedPaths.of_blocks (setCur_blocks joinRun)
    rw [← stateEqual]
    exact joinedPaths

end Goose.Lower.Validation
