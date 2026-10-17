import Goose.Lower.Validation.EmittedMetadataSourceContracts

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure EmittedMetadataAction (le : LEnv) (loop : Option LoopCtx) (action : B α) : Prop where
  metadata : EmittedMetadataRun le loop action
  dense : DenseRun action
  advance : AdvB action
  targets : GeneratedTargetRun loop action
  types : TypeRun action

theorem EmittedMetadataAction.bind {le : LEnv} {loop : Option LoopCtx}
    {first : B α} {next : α → B β} (one : EmittedMetadataAction le loop first)
    (two : ∀ value, EmittedMetadataAction le loop (next value)) :
    EmittedMetadataAction le loop (first >>= next) := by
  refine ⟨?_, DenseRun.bind one.dense (fun value => (two value).dense),
    AdvB.bind one.advance (fun value => (two value).advance),
    GeneratedTargetRun.bind one.targets (fun value => (two value).targets),
    TypeRun.bind one.types (fun value => (two value).types)⟩
  intro before result after generated loopBounds loopTypes run checked
  obtain ⟨value, middle, firstRun, nextRun⟩ := bind_eq.mp run
  have middleGenerated := generated.of_runs one.dense one.targets loopBounds firstRun
  have middleBounds := loopBounds.mono (one.advance le before value middle firstRun).ext.1
  have middleTypes := loopTypes.retained (one.types le before value middle firstRun)
  exact (two value).metadata middle result after middleGenerated middleBounds middleTypes nextRun
    (one.metadata before value middle generated loopBounds loopTypes firstRun checked)

theorem EmittedMetadataAction.pure (le : LEnv) (loop : Option LoopCtx) (value : α) :
    EmittedMetadataAction le loop (pure value) := by
  refine ⟨?_, DenseRun.pure value, AdvB.pure value, generatedTargets_pure loop value, TypeRun.pure value⟩
  intro before result after generated loopBounds loopTypes run checked
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact checked

theorem EmittedMetadataAction.emitDef (le : LEnv) (loop : Option LoopCtx) (op : Op) :
    EmittedMetadataAction le loop (Goose.Lower.emitDef op) := by
  refine ⟨?_, dense_emitDef op, advB_emitDef op, generatedTargets_emitDef loop op, types_emitDef op⟩
  intro before result after generated loopBounds loopTypes run checked
  have final := checked.emitDef op
  simpa only [run] using final

theorem EmittedMetadata.recordReadValueRootRecipe {le : LEnv} {before : LS}
    (checked : EmittedMetadata le before) (value : ValueId) (place : Place) :
    EmittedMetadata le (Goose.Lower.recordReadValueRootRecipe value place le before).2 := by
  apply checked.of_preserving (types_recordReadValueRootRecipe value place le before _ _ rfl)
  intro inst member
  have blocks : (Goose.Lower.recordReadValueRootRecipe value place le before).2.blocks = before.blocks := by
    cases place <;> simp only [recordReadValueRootRecipe_run] <;> first
      | rfl
      | (split <;> simp only [recordValueRootSource_run] <;> rfl)
  have same : (Goose.Lower.recordReadValueRootRecipe value place le before).2.insts = before.insts := by
    change List.flatMap (fun block => block.insts.toList)
      (Goose.Lower.recordReadValueRootRecipe value place le before).2.blocks.toList = _
    rw [blocks]
    rfl
  exact Or.inl (same ▸ member)

theorem EmittedMetadataAction.recordReadValueRootRecipe (le : LEnv) (loop : Option LoopCtx)
    (value : ValueId) (place : Place) :
    EmittedMetadataAction le loop (Goose.Lower.recordReadValueRootRecipe value place) := by
  refine ⟨?_, dense_recordReadValueRootRecipe value place, advB_recordReadValueRootRecipe value place,
    generatedTargets_recordReadValueRootRecipe loop value place, types_recordReadValueRootRecipe value place⟩
  intro before result after generated loopBounds loopTypes run checked
  have final := checked.recordReadValueRootRecipe value place
  simpa only [run] using final

theorem EmittedMetadataAction.withLoop {le : LEnv} {action : B α}
    (checked : EmittedMetadataAction le none action) (loop : Option LoopCtx) :
    EmittedMetadataAction le loop action := by
  refine ⟨?_, checked.dense, checked.advance, checked.targets.withLoop checked.advance loop, checked.types⟩
  intro before result after generated loopBounds loopTypes run metadata
  exact checked.metadata before result after generated trivial trivial run metadata

theorem EmittedMetadataAction.lowerExpr {le : LEnv} (expr : Expr)
    (checked : EmittedMetadataRun le none (lowerExpr expr)) :
    EmittedMetadataAction le none (lowerExpr expr) :=
  ⟨checked, dense_lowerExpr expr, advB_lowerExpr expr, generatedTargets_lowerExpr none expr, types_lowerExpr expr⟩

theorem EmittedMetadataAction.lowerPlace {le : LEnv} (place : Place)
    (checked : EmittedMetadataRun le none (lowerPlace place)) :
    EmittedMetadataAction le none (lowerPlace place) :=
  ⟨checked, dense_lowerPlace place, advB_lowerPlace place, generatedTargets_lowerPlace none place, types_lowerPlace place⟩

theorem EmittedMetadataAction.lowerView {le : LEnv} (view : View)
    (checked : EmittedMetadataRun le none (lowerView view)) :
    EmittedMetadataAction le none (lowerView view) :=
  ⟨checked, dense_lowerView view, advB_lowerView view, generatedTargets_lowerView none view, types_lowerView view⟩

theorem EmittedMetadataAction.lowerBound {le : LEnv} (bound : Bound)
    (checked : EmittedMetadataRun le none (lowerBound bound)) :
    EmittedMetadataAction le none (lowerBound bound) :=
  ⟨checked, dense_lowerBound bound, advB_lowerBound bound, generatedTargets_lowerBound none bound, types_lowerBound bound⟩

theorem EmittedMetadataAction.lowerExprs {le : LEnv} (exprs : List Expr)
    (checked : EmittedMetadataRun le none (lowerExprs exprs)) :
    EmittedMetadataAction le none (lowerExprs exprs) :=
  ⟨checked, dense_lowerExprs exprs, advB_lowerExprs exprs, generatedTargets_lowerExprs none exprs, types_lowerExprs exprs⟩

theorem EmittedMetadataAction.lowerArg {le : LEnv} (arg : Arg)
    (checked : EmittedMetadataRun le none (lowerArg arg)) :
    EmittedMetadataAction le none (lowerArg arg) :=
  ⟨checked, dense_lowerArg arg, advB_lowerArg arg, generatedTargets_lowerArg none arg, types_lowerArg arg⟩

theorem EmittedMetadataAction.lowerArgs {le : LEnv} (args : List Arg)
    (checked : EmittedMetadataRun le none (lowerArgs args)) :
    EmittedMetadataAction le none (lowerArgs args) :=
  ⟨checked, dense_lowerArgs args, advB_lowerArgs args, generatedTargets_lowerArgs none args, types_lowerArgs args⟩


theorem EmittedMetadataAction.same_instructions {le : LEnv} {loop : Option LoopCtx} {action : B α}
    (dense : DenseRun action) (advance : AdvB action) (targets : GeneratedTargetRun loop action)
    (types : TypeRun action) (same : ∀ before result after, action le before = (result, after) → after.insts = before.insts) :
    EmittedMetadataAction le loop action := by
  refine ⟨?_, dense, advance, targets, types⟩
  intro before result after generated loopBounds loopTypes run checked
  refine checked.of_preserving (types le before result after run) ?_
  intro inst member
  exact Or.inl (by simpa only [same before result after run] using member)

theorem EmittedMetadataAction.read (le : LEnv) (loop : Option LoopCtx)  :
    EmittedMetadataAction le loop (read : B (LEnv)) := by
  refine EmittedMetadataAction.same_instructions (dense_read) (advB_read)
    (generatedTargets_read loop) (types_read) ?_
  intro before result after run
  have same : after = before := (congrArg Prod.snd run).symm.trans (rfl)
  rw [same]

theorem EmittedMetadataAction.get (le : LEnv) (loop : Option LoopCtx)  :
    EmittedMetadataAction le loop (get : B (LS)) := by
  refine EmittedMetadataAction.same_instructions (dense_get) (advB_get)
    (generatedTargets_get loop) (types_get) ?_
  intro before result after run
  have same : after = before := (congrArg Prod.snd run).symm.trans (rfl)
  rw [same]

theorem EmittedMetadataAction.curBlock (le : LEnv) (loop : Option LoopCtx)  :
    EmittedMetadataAction le loop (curBlock : B (Option BlockId)) := by
  refine EmittedMetadataAction.same_instructions (dense_curBlock) (advB_curBlock)
    (generatedTargets_curBlock loop) (types_curBlock) ?_
  intro before result after run
  have same : after = before := (congrArg Prod.snd run).symm.trans (rfl)
  rw [same]

theorem EmittedMetadataAction.isLive (le : LEnv) (loop : Option LoopCtx)  :
    EmittedMetadataAction le loop (isLive : B (Bool)) := by
  refine EmittedMetadataAction.same_instructions (dense_isLive) (advB_isLive)
    (generatedTargets_isLive loop) (types_isLive) ?_
  intro before result after run
  have same : after = before := (congrArg Prod.snd run).symm.trans (rfl)
  rw [same]

theorem EmittedMetadataAction.valTy (le : LEnv) (loop : Option LoopCtx) (value : ValueId) :
    EmittedMetadataAction le loop (valTy value : B (VTy)) := by
  refine EmittedMetadataAction.same_instructions (dense_valTy value) (advB_valTy value)
    (generatedTargets_valTy loop value) (types_valTy value) ?_
  intro before result after run
  have same : after = before := (congrArg Prod.snd run).symm.trans (valTy_run value le before)
  rw [same]

theorem EmittedMetadataAction.intTyOf (le : LEnv) (loop : Option LoopCtx) (value : ValueId) :
    EmittedMetadataAction le loop (intTyOf value : B (IntTy)) := by
  refine EmittedMetadataAction.same_instructions (dense_intTyOf value) (advB_intTyOf value)
    (generatedTargets_intTyOf loop value) (types_intTyOf value) ?_
  intro before result after run
  have same : after = before := (congrArg Prod.snd run).symm.trans (intTyOf_state value le before)
  rw [same]

theorem EmittedMetadataAction.freezeTo (le : LEnv) (loop : Option LoopCtx) (mu : Mutability) (owner : ValueId) :
    EmittedMetadataAction le loop (Goose.Lower.freezeTo mu owner) := by
  unfold Goose.Lower.freezeTo
  refine (EmittedMetadataAction.valTy le loop owner).bind fun type => ?_
  split
  · exact .emitDef le loop _
  · exact .pure le loop owner

theorem EmittedMetadataAction.borrowTo (le : LEnv) (loop : Option LoopCtx) (mu : Mutability) (owner : ValueId) :
    EmittedMetadataAction le loop (Goose.Lower.borrowTo mu owner) := by
  refine ⟨?_, dense_borrowTo mu owner, advB_borrowTo mu owner, generatedTargets_borrowTo loop mu owner,
    types_borrowTo mu owner⟩
  intro before result after generated loopBounds loopTypes run checked
  rcases borrowTo_cases run with frozen | emitted
  · exact (EmittedMetadataAction.freezeTo le loop mu owner).metadata before result after generated loopBounds loopTypes frozen checked
  · simpa only [emitted] using checked.emitDef (.ownerBorrow owner)

theorem EmittedMetadataAction.coerceTo (le : LEnv) (loop : Option LoopCtx) (target : Ty)
    (value : ValueId) (origin : OriginId) : EmittedMetadataAction le loop (Goose.Lower.coerceTo target value origin) := by
  unfold Goose.Lower.coerceTo
  refine (EmittedMetadataAction.valTy le loop value).bind fun source => ?_
  split
  · exact .emitDef le loop _
  · exact (EmittedMetadataAction.emitDef le loop _).bind fun view =>
      EmittedMetadataAction.emitDef le loop (.viewSlice .readOnly view .omitted .omitted (some origin))
  · exact .pure le loop value

theorem EmittedMetadataAction.coerceSlot (le : LEnv) (loop : Option LoopCtx) (slot : SlotId)
    (value : ValueId) (origin : OriginId) : EmittedMetadataAction le loop (Goose.Lower.coerceSlot slot value origin) := by
  unfold Goose.Lower.coerceSlot
  exact (EmittedMetadataAction.read le loop).bind fun env => match env.slots[slot]? with
    | none => .pure le loop value
    | some destination => EmittedMetadataAction.coerceTo le loop destination.ty value origin

theorem EmittedMetadataAction.coerceResult (le : LEnv) (loop : Option LoopCtx)
    (value : ValueId) (origin : OriginId) : EmittedMetadataAction le loop (Goose.Lower.coerceResult value origin) := by
  unfold Goose.Lower.coerceResult
  exact (EmittedMetadataAction.read le loop).bind fun env => match env.results.head? with
    | none => .pure le loop value
    | some destination => EmittedMetadataAction.coerceTo le loop destination value origin


theorem EmittedMetadataAction.emitEffect (le : LEnv) (loop : Option LoopCtx) (effect : Effect)
    (typed : ∀ before, GeneratedBuilderState before → before.cur.isSome = true → EmittedEffectTyped le before effect) :
    EmittedMetadataAction le loop (Goose.Lower.emitEffect effect) := by
  refine ⟨?_, dense_emitEffect effect, advB_emitEffect effect, generatedTargets_emitEffect loop effect, types_emitEffect effect⟩
  intro before result after generated loopBounds loopTypes run checked
  have final := checked.emitEffect effect (typed before generated)
  simpa only [run] using final

theorem EmittedMetadataAction.emitTerm (le : LEnv) (loop : Option LoopCtx) (term : Term)
    (targets : ∀ state, LoopBuilderTargets loop state → ∀ target ∈ term.successors, target < state.blocks.size)
    (typed : ∀ before, GeneratedBuilderState before → LoopBuilderTargets loop before → EmittedLoopTypes loop before →
      before.cur.isSome = true → EmittedTermTyped le.results before term) :
    EmittedMetadataAction le loop (Goose.Lower.emitTerm term) := by
  refine ⟨?_, dense_emitTerm term, advB_emitTerm term, generatedTargets_emitTerm loop term targets, types_emitTerm term⟩
  intro before result after generated loopBounds loopTypes run checked
  have final := checked.emitTerm term (typed before generated loopBounds loopTypes)
  simpa only [run] using final

theorem EmittedMetadataAction.emitNoSuccessors (le : LEnv) (loop : Option LoopCtx) (term : Term)
    (empty : term.successors = [])
    (typed : ∀ before, GeneratedBuilderState before → before.cur.isSome = true → EmittedTermTyped le.results before term) :
    EmittedMetadataAction le loop (Goose.Lower.emitTerm term) :=
  EmittedMetadataAction.emitTerm le loop term (by simp [empty]) (fun before generated _ _ => typed before generated)

theorem EmittedMetadataAction.enter (le : LEnv) (loop : Option LoopCtx) (scope : ScopeId) :
    EmittedMetadataAction le loop (Goose.Lower.emitEffect (.enter scope)) :=
  .emitEffect le loop _ (fun _ _ _ => .enter scope)

theorem EmittedMetadataAction.leave (le : LEnv) (loop : Option LoopCtx) (scope : ScopeId) :
    EmittedMetadataAction le loop (Goose.Lower.emitEffect (.leave scope)) :=
  .emitEffect le loop _ (fun _ _ _ => .leave scope)

theorem EmittedMetadataAction.whenLive {le : LEnv} {loop : Option LoopCtx} (fallback : α)
    {action : BlockId → B α} (checked : ∀ block, EmittedMetadataAction le loop (action block)) :
    EmittedMetadataAction le loop (Goose.Lower.whenLive fallback action) := by
  simpa only [Goose.Lower.whenLive] using
    (EmittedMetadataAction.curBlock le loop).bind (fun current => match current with
      | none => EmittedMetadataAction.pure le loop fallback
      | some block => checked block)

theorem EmittedMetadataAction.inScope {le : LEnv} {loop : Option LoopCtx} (scope : ScopeId)
    {action : B α} (checked : EmittedMetadataAction le loop action) :
    EmittedMetadataAction le loop (Goose.Lower.inScope scope action) := by
  refine ⟨?_, dense_inScope scope checked.dense, advB_inScope scope checked.advance,
    generatedTargets_inScope scope checked.targets, types_inScope scope checked.types⟩
  intro before result after generated loopBounds loopTypes run metadata
  unfold Goose.Lower.inScope at run
  simp only [bind_eq] at run
  obtain ⟨ignored, entered, pushed, value, middle, bodyRun, ignored', left, popped, finished⟩ := run
  rw [pushScope_run] at pushed
  obtain ⟨_, rfl⟩ := Prod.mk.inj pushed
  rw [pure_run] at finished
  obtain ⟨_, rfl⟩ := Prod.mk.inj finished
  rw [popScope_run] at popped
  obtain ⟨_, rfl⟩ := Prod.mk.inj popped
  have active := checked.metadata { before with stack := scope :: before.stack } value middle
    ⟨generated.dense, generated.live, generated.targets⟩ loopBounds loopTypes bodyRun (metadata.pushScope scope)
  exact active.popScope


theorem EmittedMetadataAction.leaveAll (le : LEnv) (loop : Option LoopCtx) :
    ∀ scopes, EmittedMetadataAction le loop (Goose.Lower.leaveAll scopes)
  | [] => .pure le loop ()
  | scope :: rest => (EmittedMetadataAction.leave le loop scope).bind fun _ => EmittedMetadataAction.leaveAll le loop rest

theorem EmittedMetadataAction.leaveTo (le : LEnv) (loop : Option LoopCtx) (depth : Nat) :
    EmittedMetadataAction le loop (Goose.Lower.leaveTo depth) := by
  unfold Goose.Lower.leaveTo
  exact (EmittedMetadataAction.get le loop).bind fun state => EmittedMetadataAction.leaveAll le loop _

theorem EmittedMetadataAction.loopBranch (le : LEnv) (loop : Option LoopCtx) (target : BlockId) (args : List ValueId)
    (bounded : ∀ state, LoopBuilderTargets loop state → target < state.blocks.size) :
    EmittedMetadataAction le loop (Goose.Lower.emitTerm (.br target args)) := by
  apply EmittedMetadataAction.emitTerm le loop (.br target args)
  · intro state checked destination member
    have same : destination = target := by simpa only [Term.successors, List.mem_singleton] using member
    rw [same]
    exact bounded state checked
  · intro before generated loopBounds loopTypes live
    exact .br target args

end Goose.Lower.Validation
