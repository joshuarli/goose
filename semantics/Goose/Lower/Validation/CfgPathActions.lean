import Goose.Lower.Validation.CfgLoopComposition

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure PathAction (action : B α) : Prop where
  advance : AdvB action
  paths : BoundedRun ReachableBuilder action

theorem PathAction.pure (value : α) : PathAction (pure value) :=
  ⟨AdvB.pure value, BoundedRun.pure _ value⟩

theorem PathAction.bind {first : B α} {next : α → B β}
    (one : PathAction first) (two : ∀ result, PathAction (next result)) : PathAction (first >>= next) :=
  ⟨one.advance.bind (fun value => (two value).advance),
    BoundedRun.bind one.advance one.paths (fun value => (two value).paths)⟩

theorem PathAction.of_blocks {action : B α} (advance : AdvB action)
    (blocks : ∀ env state, (action env state).2.blocks = state.blocks) : PathAction action :=
  ⟨advance, paths_of_blocks_unchanged blocks⟩

theorem path_emitDef (op : Op) : PathAction (emitDef op) := ⟨advB_emitDef op, paths_emitDef op⟩
theorem path_emitEffect (effect : Effect) : PathAction (emitEffect effect) :=
  ⟨advB_emitEffect effect, paths_emitEffect effect⟩
theorem path_emitTerm (term : Term) : PathAction (emitTerm term) := ⟨advB_emitTerm term, paths_emitTerm term⟩
theorem path_valTy (value : ValueId) : PathAction (valTy value) := ⟨advB_valTy value, paths_valTy value⟩
theorem path_intTyOf (value : ValueId) : PathAction (intTyOf value) :=
  ⟨advB_intTyOf value, paths_intTyOf value⟩
theorem path_read : PathAction (read : B LEnv) := ⟨advB_read, paths_read⟩
theorem path_get : PathAction (get : B LS) := PathAction.of_blocks advB_get (fun _ _ => rfl)
theorem path_isLive : PathAction isLive := PathAction.of_blocks advB_isLive (fun _ _ => rfl)

theorem path_freezeTo (mu : Mutability) (value : ValueId) : PathAction (freezeTo mu value) := by
  refine ⟨advB_freezeTo mu value, ?_⟩
  intro env before result after run paths bounded
  rcases freezeTo_cases run with ⟨_, same⟩ | emitted
  · simpa [same] using paths
  · exact paths_emitDef _ env before result after emitted paths bounded

theorem path_coerceTo (target : Ty) (value : ValueId) (origin : OriginId) :
    PathAction (coerceTo target value origin) := by
  refine ⟨advB_coerceTo target value origin, ?_⟩
  intro env before result after run paths bounded
  rcases coerceTo_cases run with ⟨_, same⟩ | ⟨elem, _, emitted⟩ | ⟨elem, view, middle, _, first, second⟩
  · simpa [same] using paths
  · exact paths_emitDef _ env before result after emitted paths bounded
  · have middlePaths := paths_emitDef _ env before view middle first paths bounded
    have middleBound := liveBound_of_adv (adv_emitDef first) bounded
    exact paths_emitDef _ env middle result after second middlePaths middleBound

theorem path_coerceSlot (slot : SlotId) (value : ValueId) (origin : OriginId) :
    PathAction (coerceSlot slot value origin) := by
  unfold coerceSlot
  refine PathAction.bind path_read fun env => ?_
  cases env.slots[slot]? with
  | none => exact PathAction.pure _
  | some destination => exact path_coerceTo _ _ _

theorem path_coerceResult (value : ValueId) (origin : OriginId) :
    PathAction (coerceResult value origin) := by
  unfold coerceResult
  refine PathAction.bind path_read fun env => ?_
  cases env.results.head? with
  | none => exact PathAction.pure _
  | some destination => exact path_coerceTo _ _ _

theorem path_implOfContext (context : ContextId) : PathAction (implOfContext context) := by
  unfold implOfContext
  exact PathAction.bind path_read fun _ => PathAction.pure _

theorem path_growOwner (value : ValueId) : PathAction (growOwner value) := by
  unfold growOwner
  refine PathAction.bind (path_valTy value) fun ty => ?_
  cases ty with
  | data ty => cases ty <;> exact PathAction.pure _
  | view _ _ => exact PathAction.pure _

theorem path_inScope (scope : ScopeId) {action : B α} (child : PathAction action) :
    PathAction (inScope scope action) := by
  refine ⟨advB_inScope scope child.advance, ?_⟩
  intro env before result after run paths bounded
  obtain ⟨middle, childRun, same⟩ := inScope_eq run
  have beforePaths : ReachableBuilder { before with stack := scope :: before.stack } := paths.of_blocks rfl
  have beforeBound : LiveBound { before with stack := scope :: before.stack } := bounded
  have middlePaths := child.paths env _ result middle childRun beforePaths beforeBound
  exact middlePaths.of_blocks (by rw [same])

theorem path_initSlots : ∀ pre, PathAction (initSlots pre)
  | [] => PathAction.pure _
  | _ :: rest => PathAction.bind (path_emitEffect _) fun _ => path_initSlots rest

theorem path_leaveAll : ∀ scopes, PathAction (leaveAll scopes)
  | [] => PathAction.pure _
  | _ :: rest => PathAction.bind (path_emitEffect _) fun _ => path_leaveAll rest

theorem path_leaveTo (depth : Nat) : PathAction (leaveTo depth) := by
  unfold leaveTo
  exact PathAction.bind path_get fun _ => path_leaveAll _

theorem path_regrowOf (owner : Option ValueId) : PathAction (regrowOf owner) := by
  cases owner with
  | none => exact PathAction.pure _
  | some value => exact path_growOwner value

theorem path_eachSampled (regrow : Bool) (view : ValueId) : PathAction (eachSampled regrow view) := by
  unfold eachSampled
  cases regrow
  · exact path_emitDef _
  · exact PathAction.pure _

theorem path_eachElemValue (var : VarId) (byRef : Bool) (elem : ValueId) :
    PathAction (eachElemValue var byRef elem) := by
  unfold eachElemValue
  cases byRef
  · exact path_emitDef _
  · refine PathAction.bind path_read fun env => ?_
    cases env.vars[var]? with
    | none => exact PathAction.pure _
    | some localVar =>
      dsimp only
      cases localVar.ty <;> first | exact PathAction.pure _ | exact path_freezeTo _ _

theorem PathAction.live {action : B α} (child : PathAction action) : LivePathRun action :=
  LivePathRun.of_bounded child.paths

theorem path_whenLive (default : α) {action : B α} (advance : AdvB action)
    (paths : LivePathRun action) : PathAction (whenLive default fun _ => action) :=
  ⟨advB_whenLive default (fun _ => advance), paths_whenLive_live default paths⟩

theorem path_assert (condition : ValueId) (origin : OriginId) :
    PathAction (whenLive () fun _ => do
      let (passBlock, failBlock) ← fork condition
      setCur (some failBlock)
      emitTerm (.abort .assert (some origin))
      setCur (some passBlock)) := by
  refine ⟨advB_assert_core condition origin, ?_⟩
  intro env before result after run paths bounded
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact paths
  | some source =>
    rw [whenLive_some _ _ env current] at run
    simp only [bind_eq] at run
    obtain ⟨⟨passBlock, failBlock⟩, forked, forkRun, _, started, startRun,
      _, closed, closeRun, finalRun⟩ := run
    have forkPaths := paths.fork current (bounded source current) condition env
    rw [forkRun] at forkPaths
    have startedPaths := forkPaths.of_blocks (setCur_blocks startRun)
    have closedPaths := startedPaths.emitTerm (.abort .assert (some origin)) env
    rw [closeRun] at closedPaths
    exact closedPaths.of_blocks (setCur_blocks finalRun)

end Goose.Lower.Validation
