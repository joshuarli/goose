import Goose.Lower.Validation.SymbolSourceTables
import Goose.Lower.Validation.ExpressionTypingCallOps
import Goose.Lower.Validation.ScopeLexical
import Goose.Lower.Validation.ScopeBlocks

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

structure Inst.SourceSymbolsWithin (le : LEnv) (scopeCount : Nat) (inst : Inst) : Prop where
  origin : ∀ o, inst.origin = some o → o < le.mod.origins.size
  slots : ∀ s ∈ instSlotRefs inst, s < le.slots.size
  globals : ∀ g ∈ instGlobalRefs inst, g < le.globals.size
  functions : ∀ f ∈ instFunctionRefs inst, f < le.sigs.size
  scopes : ∀ sc ∈ instScopeRefs inst, sc < scopeCount

theorem Inst.SourceSymbolsWithin.def {le : LEnv} {scopeCount : Nat} {value : ValueId}
    {op : Op} (origin : ∀ o, op.origin = some o → o < le.mod.origins.size)
    (references : Op.SymbolRefsValid le op) :
    Inst.SourceSymbolsWithin le scopeCount (.def value op) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [Inst.origin] using origin
  · intro slot member
    cases op <;> simp_all [instSlotRefs, Op.SymbolRefsValid]
  · intro global member
    cases op <;> simp_all [instGlobalRefs, Op.SymbolRefsValid]
  · intro function member
    cases op <;> simp_all [instFunctionRefs, Op.SymbolRefsValid]
  · simp [instScopeRefs]

theorem Inst.SourceSymbolsWithin.eff {le : LEnv} {scopeCount : Nat} {effect : Effect}
    (origin : ∀ o, effect.origin = some o → o < le.mod.origins.size)
    (references : Effect.SymbolRefsValid le scopeCount effect) :
    Inst.SourceSymbolsWithin le scopeCount (.eff effect) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [Inst.origin] using origin
  · intro slot member
    cases effect <;> simp_all [instSlotRefs, Effect.SymbolRefsValid]
  · simp [instGlobalRefs]
  · simp [instFunctionRefs]
  · intro scope member
    cases effect <;> simp_all [instScopeRefs, Effect.SymbolRefsValid]

theorem Inst.SourceSymbolsWithin.term {le : LEnv} {scopeCount : Nat} {term : Term}
    (origin : ∀ o, term.origin = some o → o < le.mod.origins.size) :
    Inst.SourceSymbolsWithin le scopeCount (.term term) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [Inst.origin] using origin
  · simp [instSlotRefs]
  · simp [instGlobalRefs]
  · simp [instFunctionRefs]
  · simp [instScopeRefs]

def LS.SourceSymbolsWF (le : LEnv) (scopeCount : Nat) (state : LS) : Prop :=
  (∀ inst ∈ state.insts, Inst.SourceSymbolsWithin le scopeCount inst) ∧
    (∀ scope ∈ state.stack, scope < scopeCount)

def LS.SourceSymbolsRun (le : LEnv) (scopeCount : Nat) (action : B α) : Prop :=
  ∀ before result after, action le before = (result, after) →
    LS.SourceSymbolsWF le scopeCount before → LS.SourceSymbolsWF le scopeCount after

theorem LS.SourceSymbolsRun.pure {le : LEnv} {scopeCount : Nat} (value : α) :
    LS.SourceSymbolsRun le scopeCount (pure value) := by
  intro before result after run checked
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact checked

theorem LS.SourceSymbolsRun.bind {le : LEnv} {scopeCount : Nat} {action : B α}
    {next : α → B β} (first : LS.SourceSymbolsRun le scopeCount action)
    (second : ∀ value, LS.SourceSymbolsRun le scopeCount (next value)) :
    LS.SourceSymbolsRun le scopeCount (action >>= next) := by
  intro before result after run checked
  obtain ⟨value, mid, firstRun, secondRun⟩ := bind_eq.mp run
  exact second value _ _ _ secondRun (first _ _ _ firstRun checked)

theorem LS.sourceSymbols_appendInst {le : LEnv} {scopeCount : Nat} {before : LS}
    (checked : LS.SourceSymbolsWF le scopeCount before) (block : BlockId) (inst : Inst)
    (source : Inst.SourceSymbolsWithin le scopeCount inst) :
    LS.SourceSymbolsWF le scopeCount (before.appendInst block inst) := by
  refine ⟨?_, ?_⟩
  · intro next member
    have checked := checked.1
    change next ∈ (before.blocks.modify block fun current =>
      { current with insts := current.insts.push inst }).toList.flatMap (fun current => current.insts.toList) at member
    obtain ⟨current, currentMember, instructionMember⟩ := List.mem_flatMap.mp member
    obtain ⟨index, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp currentMember)
    rw [Array.getElem?_modify] at lookup
    by_cases same : block = index
    · simp only [same, ↓reduceIte] at lookup
      cases previous : before.blocks[index]? with
      | none => simp [previous] at lookup
      | some old =>
        simp only [previous, Option.map_some, Option.some.injEq] at lookup
        subst current
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at instructionMember
        rcases instructionMember with oldInstruction | fresh
        · exact checked next (by
            simp only [LS.insts, List.mem_flatMap]
            exact ⟨old, Array.mem_toList_iff.mpr (Array.mem_of_getElem? previous), oldInstruction⟩)
        · subst next
          exact source
    · simp only [same, ↓reduceIte] at lookup
      exact checked next (by
        simp only [LS.insts, List.mem_flatMap]
        exact ⟨current, Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup), instructionMember⟩)
  · simpa [LS.appendInst] using checked.2

theorem LS.SourceSymbolsRun.emitDef {le : LEnv} {scopeCount : Nat} {op : Op}
    (origin : ∀ o, op.origin = some o → o < le.mod.origins.size)
    (references : Op.SymbolRefsValid le op) :
    LS.SourceSymbolsRun le scopeCount (emitDef op) := by
  intro before result after run checked
  cases current : before.cur with
  | none =>
    rw [emitDef_none op le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitDef_run op le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    have source : Inst.SourceSymbolsWithin le scopeCount (.def before.vals.size op) :=
      Inst.SourceSymbolsWithin.def (scopeCount := scopeCount) origin references
    have appended := LS.sourceSymbols_appendInst checked block (.def before.vals.size op) source
    simpa only [LS.SourceSymbolsWF, LS.insts, LS.appendInst] using appended

theorem LS.SourceSymbolsRun.emitEffect {le : LEnv} {scopeCount : Nat} (effect : Effect)
    (origin : ∀ o, effect.origin = some o → o < le.mod.origins.size)
    (references : Effect.SymbolRefsValid le scopeCount effect) :
    LS.SourceSymbolsRun le scopeCount (emitEffect effect) := by
  intro before result after run checked
  cases current : before.cur with
  | none =>
    rw [emitEffect_none effect le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitEffect_run effect le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact LS.sourceSymbols_appendInst checked block (.eff effect)
      (Inst.SourceSymbolsWithin.eff (scopeCount := scopeCount) origin references)

theorem LS.SourceSymbolsRun.emitTerm {le : LEnv} {scopeCount : Nat} (term : Term)
    (origin : ∀ o, term.origin = some o → o < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (emitTerm term) := by
  intro before result after run checked
  cases current : before.cur with
  | none =>
    rw [emitTerm_none term le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitTerm_run term le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    have appended := LS.sourceSymbols_appendInst checked block (.term term)
      (Inst.SourceSymbolsWithin.term (scopeCount := scopeCount) origin)
    simpa only [LS.SourceSymbolsWF, LS.insts, LS.appendInst] using appended

theorem LS.SourceSymbolsRun.pushScope {le : LEnv} {scopeCount : Nat} (scope : ScopeId)
    (bounded : scope < scopeCount) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.pushScope scope) := by
  intro before result after run checked
  rw [pushScope_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  refine ⟨checked.1, ?_⟩
  intro next member
  simp only [List.mem_cons] at member
  rcases member with same | member
  · subst next
    exact bounded
  · exact checked.2 next member

theorem LS.SourceSymbolsRun.popScope {le : LEnv} {scopeCount : Nat} :
    LS.SourceSymbolsRun le scopeCount Goose.Lower.popScope := by
  intro before result after run checked
  rw [popScope_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  refine ⟨checked.1, ?_⟩
  intro next member
  cases stack : before.stack with
  | nil => simp [stack] at member
  | cons head rest =>
    simp only [stack, List.drop_succ_cons, List.drop_zero] at member
    exact checked.2 next (by rw [stack]; exact List.mem_cons.mpr (Or.inr member))

theorem LS.SourceSymbolsRun.enterScope {le : LEnv} {scopeCount scope : Nat}
    (bounded : scope < scopeCount) :
    LS.SourceSymbolsRun le scopeCount (enterScope scope) := by
  change LS.SourceSymbolsRun le scopeCount
    (Goose.Lower.emitEffect (.enter scope) >>= fun _ => Goose.Lower.pushScope scope)
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitEffect (.enter scope))
  · exact LS.SourceSymbolsRun.emitEffect (.enter scope) (by simp [Effect.origin]) (by
      simpa [Effect.SymbolRefsValid] using bounded)
  · intro _
    exact LS.SourceSymbolsRun.pushScope scope bounded

theorem LS.SourceSymbolsRun.leaveScope {le : LEnv} {scopeCount scope : Nat}
    (bounded : scope < scopeCount) :
    LS.SourceSymbolsRun le scopeCount (leaveScope scope) := by
  change LS.SourceSymbolsRun le scopeCount
    (Goose.Lower.emitEffect (.leave scope) >>= fun _ => Goose.Lower.popScope)
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitEffect (.leave scope))
  · exact LS.SourceSymbolsRun.emitEffect (.leave scope) (by simp [Effect.origin]) (by
      simpa [Effect.SymbolRefsValid] using bounded)
  · intro _
    exact LS.SourceSymbolsRun.popScope

theorem LS.SourceSymbolsRun.leaveAll {le : LEnv} {scopeCount : Nat} :
    ∀ scopes : List ScopeId, (∀ scope ∈ scopes, scope < scopeCount) →
      LS.SourceSymbolsRun le scopeCount (Goose.Lower.leaveAll scopes)
  | [], _ => by
    change LS.SourceSymbolsRun le scopeCount (Pure.pure ())
    exact LS.SourceSymbolsRun.pure ()
  | scope :: rest, bounded => by
    change LS.SourceSymbolsRun le scopeCount
      (Goose.Lower.emitEffect (.leave scope) >>= fun _ => Goose.Lower.leaveAll rest)
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitEffect (.leave scope))
    · apply LS.SourceSymbolsRun.emitEffect
      · intro origin equality
        simp [Effect.origin] at equality
      · simpa [Effect.SymbolRefsValid] using bounded scope (by simp)
    · intro _
      apply LS.SourceSymbolsRun.leaveAll
      intro next member
      exact bounded next (by simp [member])

theorem LS.SourceSymbolsRun.leaveTo {le : LEnv} {scopeCount depth : Nat} :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.leaveTo depth) := by
  intro before result after run checked
  simp only [Goose.Lower.leaveTo, bind_run, get_apply] at run
  let scopes := before.stack.take (before.stack.length - depth)
  have bounded : ∀ scope ∈ scopes, scope < scopeCount := by
    intro scope member
    exact checked.2 scope (List.mem_of_mem_take member)
  exact LS.SourceSymbolsRun.leaveAll scopes bounded before result _ run checked

theorem LS.SourceSymbolsRun.initSlots {le : LEnv} {scopeCount : Nat} :
    ∀ entries : List (SlotId × ValueId × OriginId),
      (∀ entry ∈ entries, entry.1 < le.slots.size ∧ entry.2.2 < le.mod.origins.size) →
      LS.SourceSymbolsRun le scopeCount (initSlots entries)
  | [], _ => by
    change LS.SourceSymbolsRun le scopeCount (Pure.pure ())
    exact LS.SourceSymbolsRun.pure ()
  | (slot, value, origin) :: rest, bounded => by
    change LS.SourceSymbolsRun le scopeCount
      (Goose.Lower.emitEffect (.slotInit slot value (some origin)) >>= fun _ => Goose.Lower.initSlots rest)
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitEffect (.slotInit slot value (some origin)))
    · apply LS.SourceSymbolsRun.emitEffect
      · intro emitted equality
        simp only [Effect.origin, Option.some.injEq] at equality
        cases equality
        exact (bounded (slot, value, origin) (by simp)).2
      · simpa [Effect.SymbolRefsValid] using (bounded (slot, value, origin) (by simp)).1
    · intro _
      apply LS.SourceSymbolsRun.initSlots
      intro entry member
      exact bounded entry (by simp [member])

theorem Inst.SymbolsWithin.ofSource {le : LEnv} {scopeCount valueCount blockCount : Nat}
    {inst : Inst} (source : Inst.SourceSymbolsWithin le scopeCount inst)
    (uses : ∀ v ∈ inst.uses, v < valueCount)
    (targets : ∀ b ∈ instTargetRefs inst, b < blockCount) :
    Inst.SymbolsWithin le scopeCount valueCount blockCount inst :=
  ⟨uses, source.origin, source.slots, source.globals, source.functions, source.scopes, targets⟩

theorem Core.tyExpr_call_success_context_bound {env : Core.TEnv} {context : Core.ContextId}
    {args : List Core.Arg} {origin : Core.OriginId} {ty : Core.Ty} {start finish : Nat}
    (source : Core.tyExpr env (.call context args origin) start = .ok (ty, finish)) :
    context < env.mod.contexts.size := by
  obtain ⟨ctx, _, _, _, _, contextAt, _, _, _, _⟩ := tyExpr_call_tables source
  exact (Array.getElem?_eq_some_iff.mp contextAt).1

theorem Core.tyExpr_call_success_function_reference {env : Core.TEnv}
    {context : Core.ContextId} {args : List Core.Arg} {origin : Core.OriginId}
    {ty : Core.Ty} {start finish : Nat} {le : LEnv}
    (source : Core.tyExpr env (.call context args origin) start = .ok (ty, finish))
    (sigs : le.sigs.size = env.mod.contexts.size) :
    Op.SymbolRefsValid le (.call context [] (some origin)) := by
  simpa only [Op.SymbolRefsValid] using Nat.lt_of_lt_of_eq
    (Core.tyExpr_call_success_context_bound source) sigs.symm

theorem Core.tyPlace_var_success_slot_reference {env : Core.TEnv} {le : LEnv}
    {slot : Core.VarId} {start : Nat} {info : Core.PlaceInfo} {finish : Nat}
    (source : (Core.tyPlace env (.var slot)).run start = .ok (info, finish))
    (slots : env.vars.size = le.slots.size) :
    Op.SymbolRefsValid le (.slotAddr slot) := by
  simpa [Op.SymbolRefsValid] using Nat.lt_of_lt_of_eq
    (Core.tyPlace_var_success_bound source) slots

theorem Core.tyPlace_global_success_reference {env : Core.TEnv} {le : LEnv}
    {global : Core.GlobalId} {start : Nat} {info : Core.PlaceInfo} {finish : Nat}
    (source : (Core.tyPlace env (.global global)).run start = .ok (info, finish))
    (globals : env.globalLimit ≤ le.globals.size) :
    Op.SymbolRefsValid le (.globalAddr global) := by
  simpa [Op.SymbolRefsValid] using Nat.lt_of_lt_of_le
    (Core.tyPlace_global_success_bound source) globals

theorem Core.tyPlace_elem_success_origin_bound {env : Core.TEnv} {view : Core.View}
    {index : Core.Expr} {origin : Core.OriginId} {start : Nat}
    {info : Core.PlaceInfo} {finish : Nat}
    (source : Core.tyPlace env (.elem view index origin) start = .ok (info, finish)) :
    origin < env.mod.origins.size := by
  simp only [Core.tyPlace] at source
  obtain ⟨_, _, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (checkOrg_ok _ _ _ _).mp checked |>.1

theorem Core.declare_success_slot_reference {env : Core.TEnv} {le : LEnv}
    {slot scope start finish : Nat} {localVar : Core.LocalVar}
    (source : Core.declare env slot scope start = .ok (localVar, finish))
    (slots : env.vars.size = le.slots.size) : slot < le.slots.size := by
  have declared := Core.Sound.declare_ok env slot scope start (localVar, finish) source
  have slotBound : slot < env.vars.size := (Array.getElem?_eq_some_iff.mp declared.2.1).1
  exact Nat.lt_of_lt_of_eq slotBound slots

theorem ScopeTableContains.scope_bound {parents : Array (Option ScopeId)}
    {pairs : List (ScopeId × Option ScopeId)}
    (contains : ScopeTableContains parents pairs) {scope : ScopeId} {parent : Option ScopeId}
    (member : (scope, parent) ∈ pairs) : scope < parents.size :=
  (Array.getElem?_eq_some_iff.mp (contains scope parent member)).1

theorem Core.tyExpr_slice_success_origin_bound {env : Core.TEnv} {mutability : Core.Mutability}
    {view : Core.View} {lower upper : Core.Bound} {origin : Core.OriginId} {start : Nat}
    {ty : Core.Ty} {finish : Nat}
    (source : Core.tyExpr env (.slice mutability view lower upper origin) start = .ok (ty, finish)) :
    origin < env.mod.origins.size := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, next, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (checkOrg_ok _ _ _ _).mp checked |>.1

theorem Core.tyExpr_conv_success_origin_bound {env : Core.TEnv} {kind : Core.ConvKind}
    {target : Core.Ty} {expr : Core.Expr} {origin : Core.OriginId} {start : Nat}
    {ty : Core.Ty} {finish : Nat}
    (source : Core.tyExpr env (.conv kind target expr origin) start = .ok (ty, finish)) :
    origin < env.mod.origins.size := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, next, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (checkOrg_ok _ _ _ _).mp checked |>.1

theorem Core.tyExpr_un_success_origin_bound {env : Core.TEnv} {op : Core.UnOp}
    {expr : Core.Expr} {origin : Core.OriginId} {start : Nat} {ty : Core.Ty} {finish : Nat}
    (source : Core.tyExpr env (.un op expr origin) start = .ok (ty, finish)) :
    origin < env.mod.origins.size := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, next, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (checkOrg_ok _ _ _ _).mp checked |>.1

theorem Core.tyExpr_bin_success_origin_bound {env : Core.TEnv} {op : Core.BinOp}
    {left right : Core.Expr} {origin : Core.OriginId} {start : Nat}
    {ty : Core.Ty} {finish : Nat}
    (source : Core.tyExpr env (.bin op left right origin) start = .ok (ty, finish)) :
    origin < env.mod.origins.size := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, next, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (checkOrg_ok _ _ _ _).mp checked |>.1

theorem Core.tyExpr_call_success_origin_bound {env : Core.TEnv} {context : Core.ContextId}
    {args : List Core.Arg} {origin : Core.OriginId} {start : Nat} {ty : Core.Ty}
    {finish : Nat}
    (source : Core.tyExpr env (.call context args origin) start = .ok (ty, finish)) :
    origin < env.mod.origins.size := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, next, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (checkOrg_ok _ _ _ _).mp checked |>.1

theorem Core.tyExpr_pop_success_origin_bound {env : Core.TEnv} {owner : Core.Place}
    {origin : Core.OriginId} {start : Nat} {ty : Core.Ty} {finish : Nat}
    (source : Core.tyExpr env (.pop owner origin) start = .ok (ty, finish)) :
    origin < env.mod.origins.size := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, next, shrink, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, next, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (checkOrg_ok _ _ _ _).mp checked |>.1

theorem Core.tyExpr_push_success_origin_bound {env : Core.TEnv} {owner : Core.Place}
    {expr : Core.Expr} {start : Nat} {ty : Core.Ty}
    {finish : Nat} {value : Core.OriginId}
    (source : Core.tyExpr env (.push owner expr (some value)) start = .ok (ty, finish)) :
    value < env.mod.origins.size := by
  simp only [Core.tyExpr] at source
  cases profile : env.mod.profile with
  | pilot => simp [profile, chk] at source
  | shrink =>
    simp only [profile] at source
    obtain ⟨_, next, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact (checkOrg_ok _ _ _ _).mp checked |>.1

def stmtSourceOrigin : Core.Stmt → Core.OriginId
  | .letS _ _ origin | .assign _ _ origin | .assignOp _ _ _ origin | .rebind _ _ origin
  | .expr _ origin | .append _ _ origin | .popN _ _ origin | .resize _ _ _ origin
  | .clear _ origin | .assignWhole _ _ origin | .ifS _ _ _ origin | .while _ _ origin
  | .forRange _ _ _ _ origin | .forEach _ _ _ _ _ origin | .ret _ origin | .brk origin
  | .cont origin | .print _ origin | .assertS _ origin | .abort _ origin | .exit _ origin => origin

private theorem checkOrg_bind_origin_bound {env : Core.TEnv} {origin : Core.OriginId}
    {α : Type} {next : Unit → Core.T α} {start finish : Nat} {value : α}
    (source : ((Core.checkOrg env origin) >>= next) start = .ok (value, finish)) :
    origin < env.mod.origins.size := by
  obtain ⟨_, _, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (checkOrg_ok _ _ _ _).mp checked |>.1

theorem Core.tyStmt_success_origin_bound {env after : Core.TEnv} {scope start finish : Nat}
    {stmt : Core.Stmt}
    (source : Core.tyStmt env scope stmt start = .ok (after, finish)) :
    stmtSourceOrigin stmt < env.mod.origins.size := by
  cases stmt
  case' resize owner size fill origin => cases fill
  case' ifS condition thenBlock otherwise origin => cases otherwise
  case' ret value origin => cases value
  all_goals
    simp only [stmtSourceOrigin] at ⊢
    simp only [Core.tyStmt] at source
    first
    | exact checkOrg_bind_origin_bound source
    | (obtain ⟨_, _, _, rest⟩ := (st_bind_ok _ _ _ _).mp source
       exact checkOrg_bind_origin_bound rest)

end Goose.Lower.Validation
