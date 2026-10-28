import Goose.Lower.DemandParameterPrefix
import Goose.Lower.TypedCall
import Goose.Evidence.Execution
import Goose.Lower.DemandRuntimePrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence
open Goose.Proofs.Lower (extT_finish bodyTail)

theorem initSlots_trace {cfg : Cfg} {env : Env} {cx : FnCtx} {scope : ScopeId} {instanceId : ScopeInst}
    (scopes : env.scopes.head? = some (scope, instanceId)) :
    ∀ (pre : List (SlotId × ValueId × OriginId)) (values : List (VarId × Val))
      {le : LEnv} {before after : LS} {result : Unit} {point : Pt} {frame : GIR.Frame} (state : St),
      (∀ cell ∈ pre, ∃ localVar, env.vars[cell.1]? = some localVar ∧ localVar.scope = scope) →
      initSlots pre le before = (result, after) → before.pp = some point → ExtT after cx.fn.blocks →
      Rel cfg env cx frame before → PreRel frame pre values →
      ∀ count, count ≤ values.length →
        DemandRuntimePrefix cx count ⟨point, frame, state⟩
          ⟨(point.1, point.2 + count), frame,
            { state with store := preStore env.act instanceId (values.take count) state.store }⟩
  | [], [], le, before, after, result, point, frame, state, _, _, _, _, _, _, count, bound => by
    have zero : count = 0 := by simpa using bound
    subst count
    simpa only [List.take_zero, preStore, Nat.add_zero] using (DemandRuntimePrefix.zero ⟨point, frame, state⟩)
  | (slot, id, origin) :: rest, (varId, value) :: values,
      le, before, after, result, point, frame, state, declared, lowered, atPoint, extension,
      related, ⟨sameId, cell, restCells⟩, count, bound => by
    subst varId
    cases count with
    | zero => simpa only [List.take_zero, preStore, Nat.add_zero] using (DemandRuntimePrefix.zero ⟨point, frame, state⟩)
    | succ count =>
      simp only [initSlots, bind_eq] at lowered
      obtain ⟨firstResult, middle, first, remaining⟩ := lowered
      have middleExtension := extension.of_adv (advB_initSlots rest _ _ _ _ remaining)
      obtain ⟨_, sameStack, nextPoint, instruction⟩ := emitEffect_facts first atPoint middleExtension
      obtain ⟨localVar, lookup, localScope⟩ := declared (slot, id, origin) (by simp)
      obtain ⟨outer, inner⟩ : ∃ outer, env.scopes = (scope, instanceId) :: outer := by
        cases found : env.scopes with
        | nil => simp [found] at scopes
        | cons head tail => simp [found] at scopes; exact ⟨tail, by rw [scopes]⟩
      have root := rootOf_head inner lookup localScope
      have effect : execEff cx.fn frame (.slotInit slot id (some origin)) =
          bindRoot (.local env.act instanceId slot) value >>= fun _ => pure frame := by
        simp only [execEff, slotRoot_eq related slot, root, getVal_of cell, pure_bind]
      have step : RuntimeStep cx.cfg cx.fn point frame state (point.1, point.2 + 1) frame
          { state with store := state.store.introduce (.local env.act instanceId slot) value } := by
        apply RuntimeStep.effect instruction
        rw [effect]
        rfl
      have further := initSlots_trace scopes rest values { state with store := state.store.introduce (.local env.act instanceId slot) value }
        (fun cell member => declared cell (List.mem_cons_of_mem _ member)) remaining nextPoint extension
        (related.stack_eq sameStack) restCells count (by simpa using bound)
      simpa only [List.take_succ_cons, preStore, Nat.add_assoc, Nat.add_comm 1 count] using DemandRuntimePrefix.next step further
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, _, _, impossible, _, _ => impossible.elim
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, impossible, _, _ => impossible.elim


private theorem initSlots_points {cfg : Cfg} {env : Env} {cx : FnCtx} {scope : ScopeId} {instanceId : ScopeInst}
    (scopes : env.scopes.head? = some (scope, instanceId)) :
    ∀ (pre : List (SlotId × ValueId × OriginId)) (values : List (VarId × Val))
      {le : LEnv} {before after : LS} {result : Unit} {point : Pt} {frame : GIR.Frame} (state : St),
      (∀ cell ∈ pre, ∃ localVar, env.vars[cell.1]? = some localVar ∧ localVar.scope = scope) →
      initSlots pre le before = (result, after) → before.pp = some point → ExtT after cx.fn.blocks →
      Rel cfg env cx frame before → PreRel frame pre values →
      RuntimePoint cx.cfg cx.fn point frame state →
      ∀ count, count ≤ values.length →
        RuntimePoint cx.cfg cx.fn (point.1, point.2 + count) frame
          { state with store := preStore env.act instanceId (values.take count) state.store } := by
  intro pre values le before after result point frame state declared lowered atPoint extension related cells reached count bound
  exact (initSlots_trace scopes pre values state declared lowered atPoint extension related cells count bound).reachable reached

theorem accepted_block_parameter_prologue_trace {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Core.Block} {state : St} (source : BlockSource cfg env pre block state)
    {cx : FnCtx} {before after : LS} {result : ValueId} {point : Pt} {frame : GIR.Frame}
    {loop : Option LoopCtx} {bindings : List (SlotId × ValueId × OriginId)} {want : Bool} {results : List Ty}
    (lowered : lowerBlock loop bindings want block (lowerEnv cfg.mod env.vars results) before = (result, after))
    (atPoint : before.pp = some point) (extension : ExtT after cx.fn.blocks)
    (related : Rel cfg env cx frame before) (cells : PreRel frame bindings pre)
    (count : Nat) (bound : count ≤ pre.length) :
    DemandRuntimePrefix cx (count + 1) ⟨point, frame, state⟩
      ⟨(point.1, point.2 + 1 + count), { frame with scopes := (block.scope, state.nextScope) :: frame.scopes },
        { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope (pre.take count) state.store }⟩ := by
  cases block with
  | mk scope statements value =>
    obtain ⟨entered, initialized, stmtsAfter, valueAfter, left, firstResult, stmtsResult, valueResult,
      enterLowered, slotsLowered, stmtsLowered, valueLowered, leaveLowered, finalState, _⟩ :=
      prefixBlock_unfold lowered
    have leftExtension : ExtT left cx.fn.blocks := by rw [finalState] at extension; exact extension
    have valueExtension := leftExtension.of_adv (adv_emitEffect leaveLowered)
    have stmtsExtension := valueExtension.of_adv (advB_lowerBlockValue want value _ _ _ _ valueLowered)
    have slotsExtension := stmtsExtension.of_adv (advB_lowerStmts loop statements _ _ _ _ stmtsLowered)
    have enterExtension := slotsExtension.of_adv (advB_initSlots bindings _ _ _ _ slotsLowered)
    obtain ⟨_, stack, nextPoint, instruction⟩ := emitEffect_facts enterLowered atPoint enterExtension
    let inner : GIR.Frame := { frame with scopes := (scope, state.nextScope) :: frame.scopes }
    have enterStep : RuntimeStep cx.cfg cx.fn point frame state (point.1, point.2 + 1) inner
        { state with nextScope := state.nextScope + 1 } := RuntimeStep.effect instruction rfl
    have innerRelated : Rel cfg { env with scopes := (scope, state.nextScope) :: env.scopes }
        cx inner { entered with stack := scope :: entered.stack } := by
      exact ⟨related.prof, related.slots, related.act, by simp [inner, related.scopes], related.depth,
        by simp [stack, related.stack]⟩
    have tail := initSlots_trace (cfg := cfg)
      (env := { env with scopes := (scope, state.nextScope) :: env.scopes })
      (frame := inner) rfl bindings pre { state with nextScope := state.nextScope + 1 }
      (source.preScopes cells) slotsLowered nextPoint slotsExtension innerRelated (PreRel.ext (fr := frame) (fr' := inner) rfl cells)
      count bound
    simpa [inner, Core.Block.scope] using DemandRuntimePrefix.next enterStep tail

#print axioms initSlots_trace
#print axioms accepted_block_parameter_prologue_trace

theorem accepted_block_parameter_prologue {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Core.Block} {state : St} (source : BlockSource cfg env pre block state)
    {cx : FnCtx} {before after : LS} {result : ValueId} {point : Pt} {frame : GIR.Frame}
    {loop : Option LoopCtx} {bindings : List (SlotId × ValueId × OriginId)} {want : Bool} {results : List Ty}
    (lowered : lowerBlock loop bindings want block (lowerEnv cfg.mod env.vars results) before = (result, after))
    (atPoint : before.pp = some point) (extension : ExtT after cx.fn.blocks)
    (related : Rel cfg env cx frame before) (cells : PreRel frame bindings pre)
    (reached : RuntimePoint cx.cfg cx.fn point frame state) (count : Nat) (bound : count ≤ pre.length) :
    Nonempty (ParameterPrefixCursor source count) ∧
      RuntimePoint cx.cfg cx.fn (point.1, point.2 + 1 + count)
        { frame with scopes := (block.scope, state.nextScope) :: frame.scopes }
        { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope (pre.take count) state.store } ∧
      ∀ (map : RetainedSsaMap) (world : World) (caller : Env) (callerPoint : Pt) (callerFrame : GIR.Frame),
        map.Realizes cfg.mod world caller ⟨callerPoint, callerFrame, state⟩ →
        map.Realizes cfg.mod world caller ⟨callerPoint, callerFrame,
          { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope (pre.take count) state.store }⟩ := by
  cases block with
  | mk scope statements value =>
    obtain ⟨entered, initialized, stmtsAfter, valueAfter, left, firstResult, stmtsResult, valueResult,
      enterLowered, slotsLowered, stmtsLowered, valueLowered, leaveLowered, finalState, _⟩ :=
      prefixBlock_unfold lowered
    have leftExtension : ExtT left cx.fn.blocks := by rw [finalState] at extension; exact extension
    have valueExtension := leftExtension.of_adv (adv_emitEffect leaveLowered)
    have stmtsExtension := valueExtension.of_adv (advB_lowerBlockValue want value _ _ _ _ valueLowered)
    have slotsExtension := stmtsExtension.of_adv (advB_lowerStmts loop statements _ _ _ _ stmtsLowered)
    have enterExtension := slotsExtension.of_adv (advB_initSlots bindings _ _ _ _ slotsLowered)
    obtain ⟨_, stack, nextPoint, instruction⟩ := emitEffect_facts enterLowered atPoint enterExtension
    let inner : GIR.Frame := { frame with scopes := (scope, state.nextScope) :: frame.scopes }
    have enterStep : RuntimeStep cx.cfg cx.fn point frame state (point.1, point.2 + 1) inner
        { state with nextScope := state.nextScope + 1 } := RuntimeStep.effect instruction rfl
    have innerRelated : Rel cfg { env with scopes := (scope, state.nextScope) :: env.scopes }
        cx inner { entered with stack := scope :: entered.stack } := by
      exact ⟨related.prof, related.slots, related.act, by simp [inner, related.scopes], related.depth,
        by simp [stack, related.stack]⟩
    obtain ⟨cursor⟩ := source.parameterPrefix count
    refine ⟨⟨cursor⟩, ?_, fun map world caller callerPoint callerFrame realized => cursor.retained realized⟩
    exact initSlots_points (cfg := cfg)
      (env := { env with scopes := (scope, state.nextScope) :: env.scopes })
      (frame := inner) rfl bindings pre { state with nextScope := state.nextScope + 1 }
      (source.preScopes cells) slotsLowered nextPoint slotsExtension innerRelated (PreRel.ext (fr := frame) (fr' := inner) rfl cells)
      (RuntimePoint.step reached enterStep) count bound

theorem accepted_callee_parameter_prologue {cfg : Cfg} {ctx : Context} {impl : Impl}
    {act depth : Nat} {values : List Val} {state : St}
    (source : BlockSource cfg ⟨impl.vars, act, [], depth⟩
      ((impl.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)) impl.body state)
    (arity : impl.params.size = values.length)
    (entry : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl)
      (0, 0) (callFrame impl act depth values) state) (count : Nat) (bound : count ≤ values.length) :
    Nonempty (ParameterPrefixCursor source count) ∧
      RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 1 + count)
        { (callFrame impl act depth values) with scopes := [(impl.body.scope, state.nextScope)] }
        { state with nextScope := state.nextScope + 1, store := preStore act state.nextScope (((impl.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)).take count) state.store } ∧
      ∀ (map : RetainedSsaMap) (world : World) (caller : Env) (callerPoint : Pt) (callerFrame : GIR.Frame),
        map.Realizes cfg.mod world caller ⟨callerPoint, callerFrame, state⟩ →
        map.Realizes cfg.mod world caller ⟨callerPoint, callerFrame,
          { state with nextScope := state.nextScope + 1, store := preStore act state.nextScope (((impl.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)).take count) state.store }⟩ := by
  let le := lowerEnv cfg.mod impl.vars impl.results.toList
  let body := lowerBlock none (callPre impl) false impl.body le (callEntry impl)
  have tailExtension : ExtT (bodyTail impl le body.1 body.2) (lowerContextAt cfg.mod ctx impl).blocks := by
    rw [lowerContextAt_blocks, lowerImpl_call_blocks]
    exact extT_finish _
  have bodyExtension := tailExtension.of_adv
    (advB_finishFunction impl body.1 le body.2 (finishFunction impl body.1 le body.2).1
      (bodyTail impl le body.1 body.2) rfl)
  have prologue := accepted_block_parameter_prologue source
    (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩) (by rfl)
    (callEntry_pp impl) bodyExtension (callFrame_rel cfg.mod cfg.profile ctx impl act depth values)
    (callFrame_preRel impl act depth values arity) entry count (by simp [arity, bound])
  obtain ⟨_, scopes, _⟩ := bindCallParams_frame ⟨act, [], {}, depth⟩
    ((List.range impl.params.size).zip (callEntryTypes impl)) (values.map RVal.val)
  simpa only [callFrame, scopes] using prologue

end Goose.Lower
