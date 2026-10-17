import Goose.Lower.Validation.ScopeEdges

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def ScopeLoopContext (loop : Option LoopCtx) (entry : BlockId → List ScopeId)
    (stack : List ScopeId) (blocks : Nat) : Prop :=
  match loop with
  | none => True
  | some context => ScopeLoopTargets context entry stack blocks

theorem ScopeLoopContext.advance {loop : Option LoopCtx}
    {entry exit nextEntry nextExit : BlockId → List ScopeId} {before after : LS}
    (context : ScopeLoopContext loop entry before.stack before.blocks.size)
    (advance : before.Adv after) (maps : ScopeMapAdvance before entry exit nextEntry nextExit) :
    ScopeLoopContext loop nextEntry after.stack after.blocks.size := by
  cases loop with
  | none => trivial
  | some loop => exact ScopeLoopTargets.advance context advance maps

theorem ScopeLoopContext.enter {loop : Option LoopCtx} {entry : BlockId → List ScopeId}
    {stack : List ScopeId} {blocks : Nat}
    (context : ScopeLoopContext loop entry stack blocks) (scope : ScopeId) :
    ScopeLoopContext loop entry (scope :: stack) blocks := by
  cases loop with
  | none => trivial
  | some loop => exact ScopeLoopTargets.enter context scope

structure ScopeConfiguration (parents : Array (Option ScopeId))
    (entry exit : BlockId → List ScopeId) (state : LS) : Prop where
  builder : ScopeBuilder parents entry exit state
  openCurrent : CurrentOpen state
  bounded : TargetsBounded state
  edges : ScopeEdges entry exit state

theorem ScopeConfiguration.of_state {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before after : LS}
    (config : ScopeConfiguration parents entry exit before)
    (blocks : after.blocks = before.blocks) (current : after.cur = before.cur)
    (stack : after.stack = before.stack) : ScopeConfiguration parents entry exit after := by
  refine ⟨?_, config.openCurrent.of_state blocks current, config.bounded.of_blocks blocks,
    config.edges.of_blocks blocks⟩
  constructor
  · simpa only [ScopeBlockTraces, blocks] using config.builder.traces
  · intro block live
    rw [current] at live
    rw [stack]
    exact config.builder.current block live

theorem ScopeConfiguration.emitDef {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : ScopeConfiguration parents entry exit before) (op : Op) (env : LEnv) :
    ScopeConfiguration parents entry exit (Goose.Lower.emitDef op env before).2 :=
  ⟨config.builder.emitDef op env, config.openCurrent.emitDef op env,
    config.bounded.emitDef op env, config.edges.emitDef op env⟩

theorem ScopeConfiguration.emitEffect {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : ScopeConfiguration parents entry exit before) (effect : Effect)
    (neutral : scopeNeutral (.eff effect) = true) (env : LEnv) :
    ScopeConfiguration parents entry exit (Goose.Lower.emitEffect effect env before).2 :=
  ⟨config.builder.emitNeutralEffect effect neutral env, config.openCurrent.emitEffect effect env,
    config.bounded.emitEffect effect env, config.edges.emitEffect effect env⟩

theorem ScopeConfiguration.emitTerm {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : ScopeConfiguration parents entry exit before) (term : Term)
    (neutral : scopeNeutral (.term term) = true) (env : LEnv)
    (targets : ScopeTermTargets entry before.stack term)
    (bounds : ∀ target ∈ term.successors, target < before.blocks.size) :
    ScopeConfiguration parents entry exit (Goose.Lower.emitTerm term env before).2 := by
  refine ⟨config.builder.emitNeutralTerm term neutral env, currentOpen_emitTerm before term env,
    config.bounded.emitTerm term bounds env, ?_⟩
  apply config.edges.emitTerm term env
  intro block live
  rw [config.builder.current block live]
  exact targets

theorem ScopeConfiguration.newBlock {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : ScopeConfiguration parents entry exit before) (types : List VTy) (env : LEnv) :
    ScopeConfiguration parents
      (fun block => if block = before.blocks.size then before.stack else entry block)
      (fun block => if block = before.blocks.size then before.stack else exit block)
      (Goose.Lower.newBlock types env before).2 :=
  ⟨config.builder.newBlock config.openCurrent.bound env types, config.openCurrent.newBlock types env,
    config.bounded.newBlock types env, config.edges.newBlock config.bounded env types⟩

theorem ScopeConfiguration.setCur {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : ScopeConfiguration parents entry exit before) (block : BlockId) (body : BlockB)
    (row : before.blocks[block]? = some body) (openBody : OpenBlock body)
    (stack : exit block = before.stack) (env : LEnv) :
    ScopeConfiguration parents entry exit (Goose.Lower.setCur (some block) env before).2 := by
  refine ⟨config.builder.setCur (some block) ?_ env, CurrentOpen.setCur row openBody env,
    config.bounded.setCur (some block) env, config.edges.of_blocks rfl⟩
  intro other same
  cases same
  exact stack

theorem ScopeConfiguration.setNone {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : ScopeConfiguration parents entry exit before) (env : LEnv) :
    ScopeConfiguration parents entry exit (Goose.Lower.setCur none env before).2 :=
  ⟨config.builder.setCur none (by simp) env, currentOpen_none rfl,
    config.bounded.setCur none env, config.edges.of_blocks rfl⟩

theorem ScopeConfiguration.enterScope {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : ScopeConfiguration parents entry exit before) (scope : ScopeId) (env : LEnv)
    (parent : parents[scope]?.getD none = before.stack.head?) :
    ScopeConfiguration parents entry (scopeExitUpdate before.cur (scope :: before.stack) exit)
      (Goose.Lower.Validation.enterScope scope env before).2 := by
  refine ⟨config.builder.enterScope scope env parent, ?_, ?_,
    config.edges.enterScope config.openCurrent scope env⟩
  · apply (config.openCurrent.emitEffect (.enter scope) env).of_state <;> rfl
  · apply (config.bounded.emitEffect (.enter scope) env).of_blocks
    rfl

theorem ScopeConfiguration.leaveScope {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : ScopeConfiguration parents entry exit before) (scope : ScopeId)
    (rest : List ScopeId) (env : LEnv) (stack : before.stack = scope :: rest) :
    ScopeConfiguration parents entry (scopeExitUpdate before.cur rest exit)
      (Goose.Lower.Validation.leaveScope scope env before).2 := by
  refine ⟨config.builder.leaveScope scope rest env stack, ?_, ?_,
    config.edges.leaveScope config.openCurrent scope rest env⟩
  · apply (config.openCurrent.emitEffect (.leave scope) env).of_state <;> rfl
  · apply (config.bounded.emitEffect (.leave scope) env).of_blocks
    rfl

structure ScopeFlowAction (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx) (action : B α) : Prop where
  scopes : ScopeAction parents parent action
  preserves : ∀ (env : LEnv) (before : LS) (entry exit : BlockId → List ScopeId),
    ScopeConfiguration parents entry exit before →
    ScopeLoopContext loop entry before.stack before.blocks.size → before.stack.head? = parent →
    ∃ nextEntry nextExit, ScopeConfiguration parents nextEntry nextExit (action env before).2 ∧
      ScopeMapAdvance before entry exit nextEntry nextExit

theorem ScopeFlowAction.pure (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx) (value : α) : ScopeFlowAction parents parent loop (Pure.pure value : B α) := by
  refine ⟨ScopeAction.pure parents parent value, ?_⟩
  intro env before entry exit config context head
  exact ⟨entry, exit, config, ScopeMapAdvance.refl _ _ _⟩

theorem ScopeFlowAction.bind {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    {loop : Option LoopCtx} {first : B α} {next : α → B β}
    (action : ScopeFlowAction parents parent loop first)
    (rest : ∀ value, ScopeFlowAction parents parent loop (next value)) :
    ScopeFlowAction parents parent loop (first >>= next) := by
  refine ⟨action.scopes.bind (fun value => (rest value).scopes), ?_⟩
  intro env before entry exit config context head
  obtain ⟨middleEntry, middleExit, middleConfig, firstMaps⟩ :=
    action.preserves env before entry exit config context head
  have advance := action.scopes.advance env before _ _ rfl
  have middleContext := ScopeLoopContext.advance context advance firstMaps
  have middleHead : (first env before).2.stack.head? = parent := by rw [advance.stack]; exact head
  obtain ⟨afterEntry, afterExit, afterConfig, secondMaps⟩ :=
    (rest (first env before).1).preserves env (first env before).2 middleEntry middleExit
      middleConfig middleContext middleHead
  exact ⟨afterEntry, afterExit, afterConfig, firstMaps.trans advance secondMaps⟩

theorem ScopeFlowAction.weakenLoop {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    {action : B α} (source : ScopeFlowAction parents parent none action) (loop : Option LoopCtx) :
    ScopeFlowAction parents parent loop action := by
  refine ⟨source.scopes, ?_⟩
  intro env before entry exit config context head
  exact source.preserves env before entry exit config trivial head

theorem ScopeFlowAction.observe (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx) (action : B α) (scopes : ScopeAction parents parent action)
    (same : ∀ env before, (action env before).2 = before) :
    ScopeFlowAction parents parent loop action := by
  refine ⟨scopes, ?_⟩
  intro env before entry exit config context head
  refine ⟨entry, exit, ?_, ScopeMapAdvance.refl _ _ _⟩
  rw [same]
  exact config

theorem ScopeFlowAction.emitDef (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx) (op : Op) : ScopeFlowAction parents parent loop (Goose.Lower.emitDef op) := by
  refine ⟨ScopeAction.emitDef parents parent op, ?_⟩
  intro env before entry exit config context head
  exact ⟨entry, exit, config.emitDef op env, ScopeMapAdvance.refl _ _ _⟩

theorem ScopeFlowAction.emitEffect (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx) (effect : Effect) (neutral : scopeNeutral (.eff effect) = true) :
    ScopeFlowAction parents parent loop (Goose.Lower.emitEffect effect) := by
  refine ⟨ScopeAction.emitNeutralEffect parents parent effect neutral, ?_⟩
  intro env before entry exit config context head
  exact ⟨entry, exit, config.emitEffect effect neutral env, ScopeMapAdvance.refl _ _ _⟩

theorem ScopeFlowAction.emptyTerm (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx) (term : Term) (neutral : scopeNeutral (.term term) = true)
    (empty : term.successors = []) : ScopeFlowAction parents parent loop (Goose.Lower.emitTerm term) := by
  refine ⟨ScopeAction.emitNeutralTerm parents parent term neutral, ?_⟩
  intro env before entry exit config context head
  refine ⟨entry, exit, config.emitTerm term neutral env ?_ ?_, ScopeMapAdvance.refl _ _ _⟩
  · intro target member
    rw [empty] at member
    cases member
  · intro target member
    rw [empty] at member
    cases member

theorem ScopeFlowAction.get (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx) : ScopeFlowAction parents parent loop (get : B LS) :=
  .observe parents parent loop _ (ScopeAction.get parents parent) (fun _ _ => rfl)

theorem ScopeFlowAction.read (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx) : ScopeFlowAction parents parent loop (read : B LEnv) :=
  .observe parents parent loop _ (ScopeAction.read parents parent) (fun _ _ => rfl)

theorem ScopeFlowAction.valTy (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx) (value : ValueId) : ScopeFlowAction parents parent loop (Goose.Lower.valTy value) :=
  .observe parents parent loop _ (ScopeAction.valTy parents parent value) (valTy_run value)

theorem ScopeFlowAction.curBlock (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx) : ScopeFlowAction parents parent loop Goose.Lower.curBlock :=
  .observe parents parent loop _ (ScopeAction.curBlock parents parent) (fun _ _ => rfl)

theorem ScopeFlowAction.isLive (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx) : ScopeFlowAction parents parent loop Goose.Lower.isLive :=
  .observe parents parent loop _ (ScopeAction.isLive parents parent) (fun _ _ => rfl)

theorem ScopeFlowAction.intTyOf (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx) (value : ValueId) :
    ScopeFlowAction parents parent loop (Goose.Lower.intTyOf value) := by
  unfold Goose.Lower.intTyOf
  refine (ScopeFlowAction.valTy parents parent loop value).bind fun type => ?_
  cases type with
  | data type => cases type <;> exact ScopeFlowAction.pure parents parent loop _
  | view _ _ => exact ScopeFlowAction.pure parents parent loop _

theorem ScopeFlowAction.freezeTo (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx)
    (mutability : Mutability) (value : ValueId) : ScopeFlowAction parents parent loop (Goose.Lower.freezeTo mutability value) := by
  unfold Goose.Lower.freezeTo
  refine (ScopeFlowAction.valTy parents parent loop value).bind fun type => ?_
  cases mutability <;> cases type <;> first
    | exact ScopeFlowAction.pure parents parent loop _
    | (rename_i type; cases type <;> first
      | exact ScopeFlowAction.pure parents parent loop _
      | (rename_i mutability type; cases mutability <;> first
        | exact ScopeFlowAction.pure parents parent loop _
        | exact ScopeFlowAction.emitDef parents parent loop _))

theorem ScopeFlowAction.borrowTo (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx) (mutability : Mutability) (value : ValueId) :
    ScopeFlowAction parents parent loop (Goose.Lower.borrowTo mutability value) := by
  unfold Goose.Lower.borrowTo
  refine (ScopeFlowAction.read parents parent loop).bind fun env =>
    (ScopeFlowAction.valTy parents parent loop value).bind fun type => ?_
  dsimp only
  split
  all_goals
    first
    | (simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte];
        exact ScopeFlowAction.freezeTo parents parent loop mutability value)
    | (split <;> first
        | exact ScopeFlowAction.emitDef parents parent loop _
        | exact ScopeFlowAction.freezeTo parents parent loop mutability value)

theorem ScopeFlowAction.coerceTo (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx)
    (target : Ty) (value : ValueId) (origin : OriginId) :
    ScopeFlowAction parents parent loop (Goose.Lower.coerceTo target value origin) := by
  unfold Goose.Lower.coerceTo
  refine (ScopeFlowAction.valTy parents parent loop value).bind fun source => ?_
  split
  · exact ScopeFlowAction.emitDef parents parent loop _
  · exact (ScopeFlowAction.emitDef parents parent loop _).bind fun _ => ScopeFlowAction.emitDef parents parent loop _
  · exact ScopeFlowAction.pure parents parent loop _

theorem ScopeFlowAction.coerceSlot (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx)
    (slot : SlotId) (value : ValueId) (origin : OriginId) :
    ScopeFlowAction parents parent loop (Goose.Lower.coerceSlot slot value origin) := by
  unfold Goose.Lower.coerceSlot
  refine (ScopeFlowAction.read parents parent loop).bind fun env => ?_
  cases env.slots[slot]? with
  | none => exact ScopeFlowAction.pure parents parent loop _
  | some destination => exact ScopeFlowAction.coerceTo parents parent loop _ _ _

theorem ScopeFlowAction.coerceResult (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx)
    (value : ValueId) (origin : OriginId) : ScopeFlowAction parents parent loop (Goose.Lower.coerceResult value origin) := by
  unfold Goose.Lower.coerceResult
  refine (ScopeFlowAction.read parents parent loop).bind fun env => ?_
  cases env.results.head? with
  | none => exact ScopeFlowAction.pure parents parent loop _
  | some destination => exact ScopeFlowAction.coerceTo parents parent loop _ _ _

theorem ScopeFlowAction.growOwner (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx)
    (value : ValueId) : ScopeFlowAction parents parent loop (Goose.Lower.growOwner value) := by
  unfold Goose.Lower.growOwner
  refine (ScopeFlowAction.valTy parents parent loop value).bind fun type => ?_
  cases type with
  | data type => cases type <;> first
    | exact ScopeFlowAction.pure parents parent loop _
    | (rename_i mutability target; cases target <;> exact ScopeFlowAction.pure parents parent loop _)
  | view _ _ => exact ScopeFlowAction.pure parents parent loop _

theorem ScopeFlowAction.initSlots (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx) :
    ∀ slots, ScopeFlowAction parents parent loop (Goose.Lower.initSlots slots)
  | [] => ScopeFlowAction.pure parents parent loop _
  | (slot, value, origin) :: rest =>
    (ScopeFlowAction.emitEffect parents parent loop (.slotInit slot value (some origin)) rfl).bind
      fun _ => ScopeFlowAction.initSlots parents parent loop rest

theorem ScopeFlowAction.regrowOf (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx)
    (owner : Option ValueId) : ScopeFlowAction parents parent loop (Goose.Lower.regrowOf owner) := by
  cases owner with
  | none => exact ScopeFlowAction.pure parents parent loop _
  | some value => exact ScopeFlowAction.growOwner parents parent loop value

theorem ScopeFlowAction.eachSampled (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx)
    (regrow : Bool) (view : ValueId) : ScopeFlowAction parents parent loop (Goose.Lower.eachSampled regrow view) := by
  cases regrow
  · exact ScopeFlowAction.emitDef parents parent loop _
  · exact ScopeFlowAction.pure parents parent loop _

theorem ScopeFlowAction.eachLen (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx)
    (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    ScopeFlowAction parents parent loop (Goose.Lower.eachLen regrow owner sampled) := by
  cases regrow
  · exact ScopeFlowAction.pure parents parent loop _
  · exact ScopeFlowAction.emitDef parents parent loop _

theorem ScopeFlowAction.eachElemValue (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx)
    (localId : VarId) (byRef : Bool) (element : ValueId) :
    ScopeFlowAction parents parent loop (Goose.Lower.eachElemValue localId byRef element) := by
  unfold Goose.Lower.eachElemValue
  cases byRef
  · exact ScopeFlowAction.emitDef parents parent loop _
  · refine (ScopeFlowAction.read parents parent loop).bind fun env => ?_
    cases env.vars[localId]? with
    | none => exact ScopeFlowAction.pure parents parent loop _
    | some localVar =>
      dsimp only
      cases localVar.ty with
      | ref mutability type => exact ScopeFlowAction.borrowTo parents parent loop mutability element
      | _ => exact ScopeFlowAction.pure parents parent loop _


theorem ScopeFlowAction.scoped {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    {loop : Option LoopCtx} (scope : ScopeId) {inside : B α}
    (body : ScopeFlowAction parents (some scope) loop inside)
    (parentAt : parents[scope]?.getD none = parent) :
    ScopeFlowAction parents parent loop (scopedAction scope inside) := by
  refine ⟨ScopeAction.scoped scope body.scopes parentAt, ?_⟩
  intro env before entry exit config context head
  let entered := (enterScope scope env before).2
  let enteredExit := scopeExitUpdate before.cur (scope :: before.stack) exit
  have enteredState := enterScope_state scope env before
  have enteredConfig : ScopeConfiguration parents entry enteredExit entered :=
    config.enterScope scope env (parentAt.trans head.symm)
  have enteredContext : ScopeLoopContext loop entry entered.stack entered.blocks.size := by
    rw [enteredState.2.1, enteredState.2.2]
    exact ScopeLoopContext.enter context scope
  have enteredHead : entered.stack.head? = some scope := by rw [enteredState.2.1]; rfl
  obtain ⟨middleEntry, middleExit, middleConfig, middleMaps⟩ :=
    body.preserves env entered entry enteredExit enteredConfig enteredContext enteredHead
  have bodyAdvance := body.scopes.advance env entered _ _ rfl
  have middleStack : (inside env entered).2.stack = scope :: before.stack :=
    bodyAdvance.stack.trans enteredState.2.1
  have finalConfig := middleConfig.leaveScope scope before.stack env middleStack
  refine ⟨middleEntry, scopeExitUpdate (inside env entered).2.cur before.stack middleExit, finalConfig, ?_⟩
  intro block earlier
  have enteredEarlier : block < entered.blocks.size := by rw [enteredState.2.2]; exact earlier
  have middleFrame := middleMaps block enteredEarlier
  refine ⟨middleFrame.1, ?_⟩
  intro other
  have enteredOther : entered.cur ≠ some block := by rw [enteredState.1]; exact other
  have middleOther := LS_Adv.otherCurrent bodyAdvance enteredEarlier enteredOther
  simp only [scopeExitUpdate, middleOther, ite_false]
  rw [middleFrame.2 enteredOther]
  simp only [enteredExit, scopeExitUpdate, other, ite_false]

theorem scopeCurrent_mapAdvance (before : LS) (entry exit : BlockId → List ScopeId)
    (stack : List ScopeId) : ScopeMapAdvance before entry exit entry (scopeExitUpdate before.cur stack exit) := by
  intro block earlier
  refine ⟨rfl, ?_⟩
  intro other
  simp only [scopeExitUpdate, other, ite_false]

theorem TargetsBounded.leaveAll (scopes : List ScopeId) (env : LEnv) (before : LS)
    (bounded : TargetsBounded before) : TargetsBounded (Goose.Lower.leaveAll scopes env before).2 := by
  induction scopes generalizing before with
  | nil => exact bounded
  | cons scope scopes ih =>
    simp only [Goose.Lower.leaveAll, bind_run]
    exact ih _ (bounded.emitEffect (.leave scope) env)

theorem TargetsBounded.leaveTo (depth : Nat) (env : LEnv) (before : LS)
    (bounded : TargetsBounded before) : TargetsBounded (Goose.Lower.leaveTo depth env before).2 := by
  simpa only [Goose.Lower.leaveTo, bind_run, get_apply] using bounded.leaveAll _ env before

theorem ScopeConfiguration.unwindTerm {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : ScopeConfiguration parents entry exit before) (depth : Nat) (term : Term) (env : LEnv)
    (trace : ScopeTrace parents (before.stack.drop (before.stack.length - depth)) [.term term]
      (before.stack.drop (before.stack.length - depth)))
    (targets : ScopeTermTargets entry (before.stack.drop (before.stack.length - depth)) term)
    (bounds : ∀ target ∈ term.successors, target < before.blocks.size) :
    ScopeConfiguration parents entry (scopeExitUpdate before.cur (before.stack.drop (before.stack.length - depth)) exit)
      ((Goose.Lower.leaveTo depth >>= fun _ => Goose.Lower.emitTerm term) env before).2 := by
  refine ⟨?_, currentOpen_emitTerm _ term env, ?_, config.edges.unwindTerm config.openCurrent depth term env targets⟩
  · cases live : before.cur with
    | none =>
      have same : scopeExitUpdate none (before.stack.drop (before.stack.length - depth)) exit = exit := by
        funext block
        simp [scopeExitUpdate]
      rw [same]
      simpa only [bind_run, leaveTo_none _ _ _ live, emitTerm_none _ _ live] using config.builder
    | some block =>
      have bound := config.openCurrent.bound block live
      let body := before.blocks[block]
      have row : before.blocks[block]? = some body := Array.getElem?_eq_some_iff.mpr ⟨bound, rfl⟩
      have result := config.builder.unwindTerm depth term trace env block body live row
      have same : (fun other => if other = block then before.stack.drop (before.stack.length - depth) else exit other) =
          scopeExitUpdate before.cur (before.stack.drop (before.stack.length - depth)) exit := by
        funext other
        simp [scopeExitUpdate, live, eq_comm]
      simpa only [same, live] using result
  · apply (config.bounded.leaveTo depth env before).emitTerm term _ env
    intro target member
    rw [leaveTo_size]
    exact bounds target member

theorem ScopeFlowAction.unwindReturn (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx) (values : List ValueId) (origin : Option OriginId) :
    ScopeFlowAction parents parent loop (do Goose.Lower.leaveTo 0; Goose.Lower.emitTerm (.ret values origin)) := by
  refine ⟨ScopeAction.unwindReturn parents parent values origin, ?_⟩
  intro env before entry exit config context head
  have trace : ScopeTrace parents (before.stack.drop (before.stack.length - 0)) [.term (.ret values origin)]
      (before.stack.drop (before.stack.length - 0)) := by
    simp only [Nat.sub_zero, List.drop_length]
    exact .ret (.nil [])
  have afterConfig := config.unwindTerm 0 (.ret values origin) env trace
    (by intro target member; simp [Term.successors] at member)
    (by intro target member; simp [Term.successors] at member)
  exact ⟨entry, _, afterConfig, scopeCurrent_mapAdvance before entry exit _⟩

theorem ScopeFlowAction.break (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : LoopCtx) (origin : OriginId) :
    ScopeFlowAction parents parent (some loop) (lowerStmt (some loop) (.brk origin)) := by
  refine ⟨ScopeAction.unwindBranch parents parent loop.depth loop.breakTo [], ?_⟩
  intro env before entry exit config context head
  have targets : ScopeLoopTargets loop entry before.stack before.blocks.size := context
  have afterConfig := config.unwindTerm loop.depth (.br loop.breakTo []) env (.neutral rfl (.nil _))
    targets.breakTerm (by
      intro target member
      have same : target = loop.breakTo := by simpa [Term.successors] using member
      subst target
      exact targets.breakBound)
  exact ⟨entry, _, afterConfig, scopeCurrent_mapAdvance before entry exit _⟩

theorem ScopeBuilder.unwindNext {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (valid : ScopeBuilder parents entry exit before) (depth : Nat) (type : IntTy)
    (counter : ValueId) (header : BlockId) (env : LEnv) :
    ScopeBuilder parents entry (scopeExitUpdate before.cur (before.stack.drop (before.stack.length - depth)) exit)
      (Goose.Lower.Validation.unwindNext depth type counter header env before).2 := by
  let action := Goose.Lower.Validation.unwindNext depth type counter header
  have advance : AdvB action :=
    AdvB.bind (advB_leaveTo depth) fun _ => AdvB.bind (advB_emitDef _) fun _ => advB_emitTerm _
  have size : (action env before).2.blocks.size = before.blocks.size := by
    simp only [action, Goose.Lower.Validation.unwindNext, bind_run]
    rw [emitTerm_size, emitDef_size, leaveTo_size]
  have closed : (action env before).2.cur = none := by
    simp only [action, Goose.Lower.Validation.unwindNext, bind_run]
    cases live : (Goose.Lower.emitDef (.next type counter) env (Goose.Lower.leaveTo depth env before).2).2.cur with
    | none => rw [emitTerm_none _ _ live]; exact live
    | some block => rw [emitTerm_run _ _ live]
  apply valid.closeFromTrace (advance env before _ _ rfl) size closed _
  intro block body afterBody live row afterRow
  have trace := lowerStmt_continueNext_scopeTrace depth 0 header type counter 0 env before block body live row parents
  obtain ⟨_, emittedBody, emittedRow, emittedTrace⟩ := trace
  have same : emittedBody = afterBody := Option.some.inj (emittedRow.symm.trans afterRow)
  subst emittedBody
  exact emittedTrace

theorem ScopeConfiguration.unwindNext {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : ScopeConfiguration parents entry exit before) (depth : Nat) (type : IntTy)
    (counter : ValueId) (header : BlockId) (env : LEnv)
    (target : entry header = before.stack.drop (before.stack.length - depth))
    (bound : header < before.blocks.size) :
    ScopeConfiguration parents entry (scopeExitUpdate before.cur (before.stack.drop (before.stack.length - depth)) exit)
      (Goose.Lower.Validation.unwindNext depth type counter header env before).2 := by
  refine ⟨config.builder.unwindNext depth type counter header env, currentOpen_emitTerm _ _ env, ?_,
    config.edges.unwindNext config.openCurrent depth type counter header env target⟩
  apply ((config.bounded.leaveTo depth env before).emitDef (.next type counter) env).emitTerm _ _ env
  intro destination member
  have same : destination = header := by simpa [Term.successors] using member
  subst destination
  rw [emitDef_size, leaveTo_size]
  exact bound

theorem ScopeFlowAction.continue (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : LoopCtx) (origin : OriginId) :
    ScopeFlowAction parents parent (some loop) (lowerStmt (some loop) (.cont origin)) := by
  cases continued : loop.cont with
  | jump header =>
    refine ⟨?_, ?_⟩
    · simpa only [lowerStmt, continued] using ScopeAction.unwindBranch parents parent loop.depth header []
    · intro env before entry exit config context head
      have targets : ScopeLoopTargets loop entry before.stack before.blocks.size := context
      have stack : entry header = before.stack.drop (before.stack.length - loop.depth) := by
        simpa only [continued] using targets.continueStack
      have bound : header < before.blocks.size := by simpa only [continued] using targets.continueBound
      have afterConfig := config.unwindTerm loop.depth (.br header []) env (.neutral rfl (.nil _))
        (by
          intro target member
          have same : target = header := by simpa [Term.successors] using member
          subst target
          exact stack)
        (by
          intro target member
          have same : target = header := by simpa [Term.successors] using member
          subst target
          exact bound)
      refine ⟨entry, scopeExitUpdate before.cur (before.stack.drop (before.stack.length - loop.depth)) exit,
        ?_, scopeCurrent_mapAdvance before entry exit _⟩
      simpa only [lowerStmt, continued] using afterConfig
  | next header type counter =>
    refine ⟨?_, ?_⟩
    · simpa only [lowerStmt, continued, Goose.Lower.Validation.unwindNext] using
        ScopeAction.unwindNext parents parent loop.depth type counter header
    · intro env before entry exit config context head
      have targets : ScopeLoopTargets loop entry before.stack before.blocks.size := context
      have stack : entry header = before.stack.drop (before.stack.length - loop.depth) := by
        simpa only [continued] using targets.continueStack
      have bound : header < before.blocks.size := by simpa only [continued] using targets.continueBound
      have afterConfig := config.unwindNext loop.depth type counter header env stack bound
      refine ⟨entry, scopeExitUpdate before.cur (before.stack.drop (before.stack.length - loop.depth)) exit,
        ?_, scopeCurrent_mapAdvance before entry exit _⟩
      simpa only [lowerStmt, continued, Goose.Lower.Validation.unwindNext] using afterConfig

end Goose.Lower.Validation
