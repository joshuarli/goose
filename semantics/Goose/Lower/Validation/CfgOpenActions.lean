import Goose.Lower.Validation.CfgReadRecipes
import Goose.Lower.Validation.CfgOpenHeader

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure OpenAction (action : B α) : Prop where
  advance : AdvB action
  paths : BoundedRun CurrentOpen action

theorem OpenAction.pure (value : α) : OpenAction (pure value) :=
  ⟨AdvB.pure value, BoundedRun.pure _ value⟩

theorem OpenAction.bind {first : B α} {next : α → B β}
    (one : OpenAction first) (two : ∀ result, OpenAction (next result)) : OpenAction (first >>= next) :=
  ⟨one.advance.bind (fun value => (two value).advance),
    BoundedRun.bind one.advance one.paths (fun value => (two value).paths)⟩

theorem OpenAction.of_state {action : B α} (advance : AdvB action)
    (blocks : ∀ env state, (action env state).2.blocks = state.blocks)
    (current : ∀ env state, (action env state).2.cur = state.cur) : OpenAction action :=
  ⟨advance, opens_of_state_unchanged blocks current⟩

theorem open_recordReadValueRootRecipe (value : ValueId) (place : Place) :
    OpenAction (recordReadValueRootRecipe value place) :=
  OpenAction.of_state (advB_recordReadValueRootRecipe value place)
    (fun env state => (recordReadValueRootRecipe_tables value place env state).1)
    (fun env state => (recordReadValueRootRecipe_tables value place env state).2.2)

theorem open_emitDef (op : Op) : OpenAction (emitDef op) := ⟨advB_emitDef op, opens_emitDef op⟩
theorem open_emitEffect (effect : Effect) : OpenAction (emitEffect effect) :=
  ⟨advB_emitEffect effect, opens_emitEffect effect⟩
theorem open_emitTerm (term : Term) : OpenAction (emitTerm term) := ⟨advB_emitTerm term, opens_emitTerm term⟩
theorem open_valTy (value : ValueId) : OpenAction (valTy value) := ⟨advB_valTy value, opens_valTy value⟩
theorem open_intTyOf (value : ValueId) : OpenAction (intTyOf value) :=
  ⟨advB_intTyOf value, opens_intTyOf value⟩
theorem open_read : OpenAction (read : B LEnv) := ⟨advB_read, opens_read⟩
theorem open_get : OpenAction (get : B LS) := OpenAction.of_state advB_get (fun _ _ => rfl) (fun _ _ => rfl)
theorem open_isLive : OpenAction isLive := OpenAction.of_state advB_isLive (fun _ _ => rfl) (fun _ _ => rfl)

theorem open_freezeTo (mu : Mutability) (value : ValueId) : OpenAction (freezeTo mu value) := by
  refine ⟨advB_freezeTo mu value, ?_⟩
  intro env before result after run paths bounded
  rcases freezeTo_cases run with ⟨_, same⟩ | emitted
  · simpa [same] using paths
  · exact opens_emitDef _ env before result after emitted paths bounded

theorem open_borrowTo (mu : Mutability) (value : ValueId) : OpenAction (borrowTo mu value) := by
  refine ⟨advB_borrowTo mu value, ?_⟩
  intro env before result after run paths bounded
  rcases borrowTo_cases run with frozen | emitted
  · exact (open_freezeTo mu value).paths env before result after frozen paths bounded
  · exact opens_emitDef _ env before result after emitted paths bounded

theorem open_coerceTo (target : Ty) (value : ValueId) (origin : OriginId) :
    OpenAction (coerceTo target value origin) := by
  refine ⟨advB_coerceTo target value origin, ?_⟩
  intro env before result after run paths bounded
  rcases coerceTo_cases run with ⟨_, same⟩ | ⟨elem, _, emitted⟩ | ⟨elem, view, middle, _, first, second⟩
  · simpa [same] using paths
  · exact opens_emitDef _ env before result after emitted paths bounded
  · have middlePaths := opens_emitDef _ env before view middle first paths bounded
    have middleBound := liveBound_of_adv (adv_emitDef first) bounded
    exact opens_emitDef _ env middle result after second middlePaths middleBound

theorem open_coerceSlot (slot : SlotId) (value : ValueId) (origin : OriginId) :
    OpenAction (coerceSlot slot value origin) := by
  unfold coerceSlot
  refine OpenAction.bind open_read fun env => ?_
  cases env.slots[slot]? with
  | none => exact OpenAction.pure _
  | some destination => exact open_coerceTo _ _ _

theorem open_coerceResult (value : ValueId) (origin : OriginId) :
    OpenAction (coerceResult value origin) := by
  unfold coerceResult
  refine OpenAction.bind open_read fun env => ?_
  cases env.results.head? with
  | none => exact OpenAction.pure _
  | some destination => exact open_coerceTo _ _ _

theorem open_growOwner (value : ValueId) : OpenAction (growOwner value) := by
  unfold growOwner
  refine OpenAction.bind (open_valTy value) fun ty => ?_
  cases ty with
  | data ty => cases ty <;> exact OpenAction.pure _
  | view _ _ => exact OpenAction.pure _

theorem open_inScope (scope : ScopeId) {action : B α} (child : OpenAction action) :
    OpenAction (inScope scope action) := by
  refine ⟨advB_inScope scope child.advance, ?_⟩
  intro env before result after run paths bounded
  obtain ⟨middle, childRun, same⟩ := inScope_eq run
  have beforePaths : CurrentOpen { before with stack := scope :: before.stack } := paths.of_state rfl rfl
  have beforeBound : LiveBound { before with stack := scope :: before.stack } := bounded
  have middlePaths := child.paths env _ result middle childRun beforePaths beforeBound
  exact middlePaths.of_state (by rw [same]) (by rw [same])

theorem open_initSlots : ∀ pre, OpenAction (initSlots pre)
  | [] => OpenAction.pure _
  | _ :: rest => OpenAction.bind (open_emitEffect _) fun _ => open_initSlots rest

theorem open_leaveAll : ∀ scopes, OpenAction (leaveAll scopes)
  | [] => OpenAction.pure _
  | _ :: rest => OpenAction.bind (open_emitEffect _) fun _ => open_leaveAll rest

theorem open_leaveTo (depth : Nat) : OpenAction (leaveTo depth) := by
  unfold leaveTo
  exact OpenAction.bind open_get fun _ => open_leaveAll _

theorem open_regrowOf (owner : Option ValueId) : OpenAction (regrowOf owner) := by
  cases owner with
  | none => exact OpenAction.pure _
  | some value => exact open_growOwner value

theorem open_eachSampled (regrow : Bool) (view : ValueId) : OpenAction (eachSampled regrow view) := by
  unfold eachSampled
  cases regrow
  · exact open_emitDef _
  · exact OpenAction.pure _

theorem open_eachElemValue (var : VarId) (byRef : Bool) (elem : ValueId) :
    OpenAction (eachElemValue var byRef elem) := by
  unfold eachElemValue
  cases byRef
  · exact open_emitDef _
  · refine OpenAction.bind open_read fun env => ?_
    cases env.vars[var]? with
    | none => exact OpenAction.pure _
    | some localVar =>
      dsimp only
      cases localVar.ty <;> first | exact OpenAction.pure _ | exact open_borrowTo _ _

theorem OpenAction.live {action : B α} (child : OpenAction action) : LiveOpenRun action :=
  LiveOpenRun.of_bounded child.paths

theorem open_whenLive (default : α) {action : B α} (advance : AdvB action)
    (paths : LiveOpenRun action) : OpenAction (whenLive default fun _ => action) :=
  ⟨advB_whenLive default (fun _ => advance), opens_whenLive_live default paths⟩

theorem open_assert (condition : ValueId) (origin : OriginId) :
    OpenAction (whenLive () fun _ => do
      let (passBlock, failBlock) ← fork condition
      setCur (some failBlock)
      emitTerm (.abort .assert (some origin))
      setCur (some passBlock)) := by
  refine ⟨advB_assert_core condition origin, ?_⟩
  intro env before result after run _ bounded
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact currentOpen_none current
  | some source =>
    rw [whenLive_some _ _ env current] at run
    simp only [bind_eq] at run
    obtain ⟨⟨passBlock, failBlock⟩, forked, forkRun, _, started, startRun,
      _, closed, closeRun, finalRun⟩ := run
    have targets := fork_open_targets current (bounded source current) condition env
    rw [forkRun] at targets
    obtain ⟨body, row, openBody⟩ := targets.1
    have startedRow : started.blocks[passBlock]? = some body := by
      simpa [setCur_blocks startRun] using row
    have distinct := fork_distinct current forkRun
    have different : started.cur ≠ some passBlock := by
      rw [setCur_current startRun]
      exact fun equality => distinct (Option.some.inj equality).symm
    exact restore_currentOpen startedRow openBody different (adv_emitTerm closeRun) finalRun

end Goose.Lower.Validation
