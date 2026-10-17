import Goose.Lower.Validation.SnapshotContentsActions
import Goose.Lower.GeneratedTargetFramesSource

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure SnapshotSourceAction (le : LEnv) (loop : Option LoopCtx) (action : B α) : Prop where
  snapshots : SnapshotTraceRun le loop action
  dense : DenseRun action
  advance : AdvB action
  targets : GeneratedTargetRun loop action
  types : TypeRun action
  frames : GeneratedTargetFrameRun loop action

theorem SnapshotSourceAction.bind {le : LEnv} {loop : Option LoopCtx}
    {first : B α} {next : α → B β}
    (one : SnapshotSourceAction le loop first)
    (two : ∀ value, SnapshotSourceAction le loop (next value)) :
    SnapshotSourceAction le loop (first >>= next) :=
  ⟨one.snapshots.bind (fun value => (two value).snapshots) one.dense one.advance one.targets
      (fun value => (two value).dense) (fun value => (two value).advance)
      (fun value => (two value).types) (fun value => (two value).frames),
    DenseRun.bind one.dense (fun value => (two value).dense),
    AdvB.bind one.advance (fun value => (two value).advance),
    GeneratedTargetRun.bind one.targets (fun value => (two value).targets),
    TypeRun.bind one.types (fun value => (two value).types),
    GeneratedTargetFrameRun.bind one.frames (fun value => (two value).frames)⟩

theorem SnapshotSourceAction.pure (le : LEnv) (loop : Option LoopCtx) (value : α) :
    SnapshotSourceAction le loop (pure value) :=
  ⟨.pure value, DenseRun.pure value, AdvB.pure value, generatedTargets_pure loop value,
    TypeRun.pure value, generatedTargetFrame_pure loop value⟩

theorem SnapshotSourceAction.emitDef (le : LEnv) (loop : Option LoopCtx) (op : Op)
    (notSnapshot : ∀ mode owner, op ≠ .snapshot mode owner) :
    SnapshotSourceAction le loop (Goose.Lower.emitDef op) :=
  ⟨.emitDef op notSnapshot, dense_emitDef op, advB_emitDef op, generatedTargets_emitDef loop op,
    types_emitDef op, generatedTargetFrame_emitDef loop op⟩

theorem SnapshotSourceAction.lowerExpr {le : LEnv} (expr : Expr)
    (source : SnapshotTraceRun le none (lowerExpr expr)) :
    SnapshotSourceAction le none (lowerExpr expr) :=
  ⟨source, dense_lowerExpr expr, advB_lowerExpr expr, generatedTargets_lowerExpr none expr,
    types_lowerExpr expr, generatedTargetFrame_lowerExpr none expr⟩

theorem SnapshotSourceAction.lowerPlace {le : LEnv} (place : Place)
    (source : SnapshotTraceRun le none (lowerPlace place)) :
    SnapshotSourceAction le none (lowerPlace place) :=
  ⟨source, dense_lowerPlace place, advB_lowerPlace place, generatedTargets_lowerPlace none place,
    types_lowerPlace place, generatedTargetFrame_lowerPlace none place⟩

theorem SnapshotSourceAction.lowerView {le : LEnv} (view : View)
    (source : SnapshotTraceRun le none (lowerView view)) :
    SnapshotSourceAction le none (lowerView view) :=
  ⟨source, dense_lowerView view, advB_lowerView view, generatedTargets_lowerView none view,
    types_lowerView view, generatedTargetFrame_lowerView none view⟩

theorem SnapshotSourceAction.lowerBound {le : LEnv} (bound : Bound)
    (source : SnapshotTraceRun le none (lowerBound bound)) :
    SnapshotSourceAction le none (lowerBound bound) :=
  ⟨source, dense_lowerBound bound, advB_lowerBound bound, generatedTargets_lowerBound none bound,
    types_lowerBound bound, generatedTargetFrame_lowerBound none bound⟩

theorem SnapshotSourceAction.lowerExprs {le : LEnv} (exprs : List Expr)
    (source : SnapshotTraceRun le none (lowerExprs exprs)) :
    SnapshotSourceAction le none (lowerExprs exprs) :=
  ⟨source, dense_lowerExprs exprs, advB_lowerExprs exprs, generatedTargets_lowerExprs none exprs,
    types_lowerExprs exprs, generatedTargetFrame_lowerExprs none exprs⟩

theorem SnapshotSourceAction.lowerArg {le : LEnv} (arg : Arg)
    (source : SnapshotTraceRun le none (lowerArg arg)) :
    SnapshotSourceAction le none (lowerArg arg) :=
  ⟨source, dense_lowerArg arg, advB_lowerArg arg, generatedTargets_lowerArg none arg,
    types_lowerArg arg, generatedTargetFrame_lowerArg none arg⟩

theorem SnapshotSourceAction.lowerArgs {le : LEnv} (args : List Arg)
    (source : SnapshotTraceRun le none (lowerArgs args)) :
    SnapshotSourceAction le none (lowerArgs args) :=
  ⟨source, dense_lowerArgs args, advB_lowerArgs args, generatedTargets_lowerArgs none args,
    types_lowerArgs args, generatedTargetFrame_lowerArgs none args⟩

theorem SnapshotSourceAction.read (le : LEnv) (loop : Option LoopCtx)  :
    SnapshotSourceAction le loop (read : B LEnv) := by
  refine ⟨SnapshotTraceRun.same_values (dense_read) (advB_read) (types_read)
    (generatedTargetFrame_read loop) ?_, dense_read, advB_read, generatedTargets_read loop,
    types_read, generatedTargetFrame_read loop⟩
  intro before result after run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run; rfl

theorem SnapshotSourceAction.valTy (le : LEnv) (loop : Option LoopCtx) (value : ValueId) :
    SnapshotSourceAction le loop (valTy value : B VTy) := by
  refine ⟨SnapshotTraceRun.same_values (dense_valTy value) (advB_valTy value) (types_valTy value)
    (generatedTargetFrame_valTy loop value) ?_, dense_valTy value, advB_valTy value, generatedTargets_valTy loop value,
    types_valTy value, generatedTargetFrame_valTy loop value⟩
  intro before result after run
  have same := congrArg Prod.snd run; exact congrArg (fun state : LS => state.vals.size) ((valTy_run value le before).symm.trans same) |>.symm

theorem SnapshotSourceAction.intTyOf (le : LEnv) (loop : Option LoopCtx) (value : ValueId) :
    SnapshotSourceAction le loop (intTyOf value : B IntTy) := by
  refine ⟨SnapshotTraceRun.same_values (dense_intTyOf value) (advB_intTyOf value) (types_intTyOf value)
    (generatedTargetFrame_intTyOf loop value) ?_, dense_intTyOf value, advB_intTyOf value, generatedTargets_intTyOf loop value,
    types_intTyOf value, generatedTargetFrame_intTyOf loop value⟩
  intro before result after run
  have same := congrArg Prod.snd run; exact congrArg (fun state : LS => state.vals.size) ((intTyOf_state value le before).symm.trans same) |>.symm

theorem SnapshotSourceAction.freezeTo (le : LEnv) (loop : Option LoopCtx) (mu : Mutability) (owner : ValueId) :
    SnapshotSourceAction le loop (Goose.Lower.freezeTo mu owner) := by
  refine ⟨?_, dense_freezeTo mu owner, advB_freezeTo mu owner, generatedTargets_freezeTo loop mu owner,
    types_freezeTo mu owner, generatedTargetFrame_freezeTo loop mu owner⟩
  intro before result after generated frames run
  exact (SnapshotSourceTrace.empty le before generated.dense).freezeTo generated run

theorem SnapshotSourceAction.borrowTo (le : LEnv) (loop : Option LoopCtx) (mu : Mutability) (owner : ValueId) :
    SnapshotSourceAction le loop (Goose.Lower.borrowTo mu owner) := by
  refine ⟨?_, dense_borrowTo mu owner, advB_borrowTo mu owner, generatedTargets_borrowTo loop mu owner,
    types_borrowTo mu owner, generatedTargetFrame_borrowTo loop mu owner⟩
  intro before result after generated frames run
  exact (SnapshotSourceTrace.empty le before generated.dense).borrowTo generated run


theorem SnapshotSourceAction.withLoop {le : LEnv} {action : B α}
    (source : SnapshotSourceAction le none action) (loop : Option LoopCtx) :
    SnapshotSourceAction le loop action :=
  ⟨(fun before result after generated _frames run => source.snapshots before result after generated trivial run),
    source.dense, source.advance, source.targets.withLoop source.advance loop, source.types, source.frames.withLoop⟩

theorem SnapshotSourceAction.get (le : LEnv) (loop : Option LoopCtx) :
    SnapshotSourceAction le loop (get : B LS) := by
  refine ⟨SnapshotTraceRun.same_values dense_get advB_get types_get
    (generatedTargetFrame_get loop) ?_, dense_get, advB_get, generatedTargets_get loop,
    types_get, generatedTargetFrame_get loop⟩
  intro before result after run
  have same : after = before := by
    exact (congrArg Prod.snd run).symm
  rw [same]

theorem SnapshotSourceAction.curBlock (le : LEnv) (loop : Option LoopCtx) :
    SnapshotSourceAction le loop (curBlock : B (Option BlockId)) := by
  refine ⟨SnapshotTraceRun.same_values dense_curBlock advB_curBlock types_curBlock
    (generatedTargetFrame_curBlock loop) ?_, dense_curBlock, advB_curBlock, generatedTargets_curBlock loop,
    types_curBlock, generatedTargetFrame_curBlock loop⟩
  intro before result after run
  have same : after = before := by
    exact (congrArg Prod.snd run).symm
  rw [same]

theorem SnapshotSourceAction.isLive (le : LEnv) (loop : Option LoopCtx) :
    SnapshotSourceAction le loop (isLive : B Bool) := by
  refine ⟨SnapshotTraceRun.same_values dense_isLive advB_isLive types_isLive
    (generatedTargetFrame_isLive loop) ?_, dense_isLive, advB_isLive, generatedTargets_isLive loop,
    types_isLive, generatedTargetFrame_isLive loop⟩
  intro before result after run
  have same : after = before := by
    exact (congrArg Prod.snd run).symm
  rw [same]

theorem SnapshotSourceAction.emitEffect (le : LEnv) (loop : Option LoopCtx) (effect : Effect) :
    SnapshotSourceAction le loop (Goose.Lower.emitEffect effect) := by
  refine ⟨SnapshotTraceRun.same_values (dense_emitEffect effect) (advB_emitEffect effect) (types_emitEffect effect)
    (generatedTargetFrame_emitEffect loop effect) ?_, dense_emitEffect effect, advB_emitEffect effect, generatedTargets_emitEffect loop effect,
    types_emitEffect effect, generatedTargetFrame_emitEffect loop effect⟩
  intro before result after run
  cases live : before.cur with
  | none => rw [emitEffect_none effect le live] at run; obtain ⟨_, rfl⟩ := Prod.mk.inj run; rfl
  | some block => rw [emitEffect_run effect le live] at run; obtain ⟨_, rfl⟩ := Prod.mk.inj run; rfl

theorem SnapshotSourceAction.emitTerm (le : LEnv) (loop : Option LoopCtx) (term : Term) (empty : term.successors = []) :
    SnapshotSourceAction le loop (Goose.Lower.emitTerm term) := by
  refine ⟨SnapshotTraceRun.same_values (dense_emitTerm term) (advB_emitTerm term) (types_emitTerm term)
    (generatedTargetFrame_emitNoSuccessors loop term empty) ?_, dense_emitTerm term, advB_emitTerm term, generatedTargets_emitTerm loop term (by simp [empty]),
    types_emitTerm term, generatedTargetFrame_emitNoSuccessors loop term empty⟩
  intro before result after run
  cases live : before.cur with
  | none => rw [emitTerm_none term le live] at run; obtain ⟨_, rfl⟩ := Prod.mk.inj run; rfl
  | some block => rw [emitTerm_run term le live] at run; obtain ⟨_, rfl⟩ := Prod.mk.inj run; rfl

theorem SnapshotSourceAction.whenLive {le : LEnv} {loop : Option LoopCtx} (fallback : α)
    {action : BlockId → B α} (checked : ∀ block, SnapshotSourceAction le loop (action block)) :
    SnapshotSourceAction le loop (Goose.Lower.whenLive fallback action) := by
  simpa only [Goose.Lower.whenLive] using
    (SnapshotSourceAction.curBlock le loop).bind (fun current => match current with
      | none => SnapshotSourceAction.pure le loop fallback
      | some block => checked block)

theorem SnapshotSourceAction.initSlots (le : LEnv) (loop : Option LoopCtx) :
    ∀ slots, SnapshotSourceAction le loop (Goose.Lower.initSlots slots)
  | [] => .pure le loop ()
  | (slot, value, origin) :: rest =>
    (SnapshotSourceAction.emitEffect le loop (.slotInit slot value (some origin))).bind fun _ =>
      SnapshotSourceAction.initSlots le loop rest


theorem SnapshotSourceAction.coerceTo (le : LEnv) (loop : Option LoopCtx) (target : Ty)
    (value : ValueId) (origin : OriginId) : SnapshotSourceAction le loop (Goose.Lower.coerceTo target value origin) := by
  unfold Goose.Lower.coerceTo
  refine (SnapshotSourceAction.valTy le loop value).bind fun source => ?_
  split
  · exact .emitDef le loop _ (by intros; intro h; cases h)
  · exact (SnapshotSourceAction.emitDef le loop _ (by intros; intro h; cases h)).bind fun view =>
      SnapshotSourceAction.emitDef le loop (.viewSlice .readOnly view .omitted .omitted (some origin))
        (by intros; intro h; cases h)
  · exact .pure le loop value

theorem SnapshotSourceAction.coerceSlot (le : LEnv) (loop : Option LoopCtx) (slot : SlotId)
    (value : ValueId) (origin : OriginId) : SnapshotSourceAction le loop (Goose.Lower.coerceSlot slot value origin) := by
  unfold Goose.Lower.coerceSlot
  exact (SnapshotSourceAction.read le loop).bind fun env => match env.slots[slot]? with
    | none => .pure le loop value
    | some destination => SnapshotSourceAction.coerceTo le loop destination.ty value origin

theorem SnapshotSourceAction.coerceResult (le : LEnv) (loop : Option LoopCtx)
    (value : ValueId) (origin : OriginId) : SnapshotSourceAction le loop (Goose.Lower.coerceResult value origin) := by
  unfold Goose.Lower.coerceResult
  exact (SnapshotSourceAction.read le loop).bind fun env => match env.results.head? with
    | none => .pure le loop value
    | some destination => SnapshotSourceAction.coerceTo le loop destination value origin

theorem SnapshotSourceAction.leaveAll (le : LEnv) (loop : Option LoopCtx) :
    ∀ scopes, SnapshotSourceAction le loop (Goose.Lower.leaveAll scopes)
  | [] => .pure le loop ()
  | scope :: rest => (SnapshotSourceAction.emitEffect le loop (.leave scope)).bind fun _ =>
      SnapshotSourceAction.leaveAll le loop rest

theorem SnapshotSourceAction.leaveTo (le : LEnv) (loop : Option LoopCtx) (depth : Nat) :
    SnapshotSourceAction le loop (Goose.Lower.leaveTo depth) := by
  unfold Goose.Lower.leaveTo
  exact (SnapshotSourceAction.get le loop).bind fun state => SnapshotSourceAction.leaveAll le loop _


theorem SnapshotSourceAction.emitTermTargets (le : LEnv) (loop : Option LoopCtx) (term : Term)
    (targets : ∀ state, LoopBuilderTargets loop state → ∀ target ∈ term.successors, target < state.blocks.size)
    (frames : ∀ target ∈ term.successors, LoopBuilderFrameTarget loop target) :
    SnapshotSourceAction le loop (Goose.Lower.emitTerm term) := by
  have framed := generatedTargetFrame_emitTerm loop term (fun _ target member _ => frames target member)
  refine ⟨SnapshotTraceRun.same_values (dense_emitTerm term) (advB_emitTerm term) (types_emitTerm term)
    framed ?_, dense_emitTerm term, advB_emitTerm term, generatedTargets_emitTerm loop term targets,
    types_emitTerm term, framed⟩
  intro before result after run
  cases live : before.cur with
  | none => rw [emitTerm_none term le live] at run; obtain ⟨_, rfl⟩ := Prod.mk.inj run; rfl
  | some block => rw [emitTerm_run term le live] at run; obtain ⟨_, rfl⟩ := Prod.mk.inj run; rfl


theorem SnapshotSourceAction.inScope {le : LEnv} {loop : Option LoopCtx} (scope : ScopeId)
    {action : B α} (checked : SnapshotSourceAction le loop action) :
    SnapshotSourceAction le loop (Goose.Lower.inScope scope action) := by
  refine ⟨?_, dense_inScope scope checked.dense, advB_inScope scope checked.advance,
    generatedTargets_inScope scope checked.targets, types_inScope scope checked.types,
    generatedTargetFrame_inScope scope checked.frames⟩
  intro before result after generated frames run
  unfold Goose.Lower.inScope at run
  simp only [bind_eq] at run
  obtain ⟨ignored, entered, pushed, value, middle, bodyRun, ignored', left, popped, finished⟩ := run
  rw [pushScope_run] at pushed
  obtain ⟨_, rfl⟩ := Prod.mk.inj pushed
  rw [pure_run] at finished
  obtain ⟨_, rfl⟩ := Prod.mk.inj finished
  rw [popScope_run] at popped
  obtain ⟨_, rfl⟩ := Prod.mk.inj popped
  have child := checked.snapshots { before with stack := scope :: before.stack } value middle
    ⟨generated.dense, generated.live, generated.targets⟩ frames bodyRun
  intro snapshot mode owner member bound
  obtain ⟨site, fresh, extension, typed, retained⟩ := child snapshot mode owner member bound
  refine ⟨site, fresh, extension, typed, ?_⟩
  intro authorized witness
  have kept := retained authorized witness
  exact ⟨kept.closed, kept.noninteger, kept.ownerMember, kept.fresh, kept.beforeSnapshot⟩


theorem SnapshotSourceAction.loopBranch (le : LEnv) (loop : Option LoopCtx) (target : BlockId) (args : List ValueId)
    (bounded : ∀ state, LoopBuilderTargets loop state → target < state.blocks.size)
    (framed : LoopBuilderFrameTarget loop target) :
    SnapshotSourceAction le loop (Goose.Lower.emitTerm (.br target args)) := by
  apply SnapshotSourceAction.emitTermTargets le loop (.br target args)
  · intro state checked destination member
    have same : destination = target := by simpa only [Term.successors, List.mem_singleton] using member
    rw [same]
    exact bounded state checked
  · intro destination member
    have same : destination = target := by simpa only [Term.successors, List.mem_singleton] using member
    rw [same]
    exact framed


theorem SnapshotSourceAction.growOwner (le : LEnv) (loop : Option LoopCtx) (owner : ValueId) :
    SnapshotSourceAction le loop (Goose.Lower.growOwner owner) := by
  unfold Goose.Lower.growOwner
  refine (SnapshotSourceAction.valTy le loop owner).bind fun type => ?_
  cases type with
  | data type =>
    cases type with
    | ref mu type =>
      cases type with
      | grow element => exact .pure le loop true
      | growshrink element => exact .pure le loop true
      | _ => exact .pure le loop false
    | _ => exact .pure le loop false
  | view _ _ => exact .pure le loop false

theorem SnapshotSourceAction.regrowOf (le : LEnv) (loop : Option LoopCtx) (owner : Option ValueId) :
    SnapshotSourceAction le loop (Goose.Lower.regrowOf owner) := by
  cases owner with
  | none => exact .pure le loop false
  | some value => exact SnapshotSourceAction.growOwner le loop value

theorem SnapshotSourceAction.eachSampled (le : LEnv) (loop : Option LoopCtx) (regrow : Bool) (view : ValueId) :
    SnapshotSourceAction le loop (Goose.Lower.eachSampled regrow view) := by
  cases regrow
  · exact .emitDef le loop (.viewLen view) (by intros; intro h; cases h)
  · exact .pure le loop 0

theorem SnapshotSourceAction.eachLen (le : LEnv) (loop : Option LoopCtx) (regrow : Bool)
    (owner : Option ValueId) (sampled : ValueId) : SnapshotSourceAction le loop (Goose.Lower.eachLen regrow owner sampled) := by
  cases regrow
  · exact .pure le loop sampled
  · exact .emitDef le loop (.arrayLen (owner.getD 0)) (by intros; intro h; cases h)

theorem SnapshotSourceAction.eachElemValue (le : LEnv) (loop : Option LoopCtx) (slot : VarId) (byRef : Bool) (elem : ValueId) :
    SnapshotSourceAction le loop (Goose.Lower.eachElemValue slot byRef elem) := by
  unfold Goose.Lower.eachElemValue
  cases byRef
  · exact .emitDef le loop (.load elem) (by intros; intro h; cases h)
  · simp only [ite_true]
    refine (SnapshotSourceAction.read le loop).bind fun env => ?_
    split
    · split
      · exact SnapshotSourceAction.borrowTo le loop _ elem
      · exact .pure le loop elem
    · exact .pure le loop elem

end Goose.Lower.Validation
