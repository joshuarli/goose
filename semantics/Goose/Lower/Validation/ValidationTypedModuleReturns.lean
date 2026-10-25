import Goose.Lower.Validation.ValidationTypedModuleTables
import Goose.Core.Sound.Invert

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem accepted_context_tail_result {module : Core.Module} {context : Context} {impl : Core.Impl}
    (accepted : Core.validate module = .ok ()) {contextIndex : Nat}
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    (tail : impl.body.value.isSome = true) :
    ∃ type finish, Core.tyBlock (implEnv module impl) [] impl.body impl.params.size = .ok (type, finish) ∧
      impl.results.toList = [type] := by
  obtain ⟨found, foundAt, checked⟩ := (validate_modOk module accepted).ctx contextIndex context contextAt
  have same : found = impl := Option.some.inj (foundAt.symm.trans implAt)
  subst found
  obtain ⟨roots, range, state, replay, resultCheck, summary⟩ := checked.body
  obtain ⟨declared, rootShape, _⟩ := (checkResultV_ok _ _ (resultCheck tail)).2
  have resultCount : impl.results.size = 1 := by
    rw [← checked.resultLen, rootShape]
    rfl
  obtain ⟨type, finish, typed, shape⟩ := ((validate_modOk module accepted).impl context.impl impl implAt).body
  refine ⟨type, finish, typed, ?_⟩
  rcases shape with ⟨empty, _⟩ | ⟨result, results, sameType, _⟩
  · have count := congrArg List.length empty
    simp [resultCount] at count
  · rw [sameType tail]
    exact results

theorem lowerBlock_tail_generated_typed (body : Core.Block)
    {env : Core.TEnv} {type : Ty} {start finish : Nat}
    (source : Core.tyBlock env [] body start = .ok (type, finish))
    (tail : body.value.isSome = true)
    (pre : List (SlotId × ValueId × OriginId)) (want : Bool)
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerBlock none pre want body (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) (generated : GeneratedBuilderState before) :
    after.vals[value]? = some (some (.data type)) := by
  cases body with
  | mk scope statements expression =>
    cases expression with
    | none => simp [Core.Block.value] at tail
    | some expr =>
      unfold Core.tyBlock at source
      by_cases nested : scope ∈ env.scopes
      · simp [nested, chk] at source
      · simp only [List.contains_iff_mem, nested, ite_false] at source
        obtain ⟨declared, declaredFinish, declaration, source⟩ := (st_bind_ok _ _ _ _).mp source
        obtain ⟨finalEnv, valueStart, statementsTyped, source⟩ := (st_bind_ok _ _ _ _).mp source
        have sameEnv : lowerEnv finalEnv.mod finalEnv.vars results = lowerEnv env.mod env.vars results :=
          (tyStmts_lowerEnv statementsTyped results).trans (declarePre_lowerEnv declaration results)
        simp only [lowerBlock, inScope] at run
        obtain ⟨_, entered, enterRun, run⟩ := bind_eq.mp run
        obtain ⟨_, pushed, pushRun, run⟩ := bind_eq.mp run
        obtain ⟨result, bodyAfter, bodyRun, run⟩ := bind_eq.mp run
        obtain ⟨_, popped, popRun, run⟩ := bind_eq.mp run
        obtain ⟨resultEq, stateEq⟩ := pure_eq.mp run
        subst after
        subst value
        obtain ⟨_, initialized, initRun, bodyRun⟩ := bind_eq.mp bodyRun
        obtain ⟨_, statementsAfter, statementsRun, bodyRun⟩ := bind_eq.mp bodyRun
        obtain ⟨result, valueAfter, valueRun, bodyRun⟩ := bind_eq.mp bodyRun
        obtain ⟨_, left, leaveRun, bodyRun⟩ := bind_eq.mp bodyRun
        obtain ⟨rfl, rfl⟩ := pure_eq.mp bodyRun
        have poppedLive := dead_popScope.live_before popRun live
        have valueLive := (dead_emitEffect (.leave scope)).live_before leaveRun poppedLive
        have enteredGenerated := generated.emitEffect (.enter scope) enterRun
        have pushedGenerated : GeneratedBuilderState pushed := by
          rw [pushScope_run] at pushRun
          obtain ⟨_, rfl⟩ := Prod.mk.inj pushRun
          exact ⟨enteredGenerated.dense, enteredGenerated.live, enteredGenerated.targets⟩
        have initializedGenerated := pushedGenerated.initSlots pre initRun
        have statementsGenerated := initializedGenerated.lowerStmts none statements trivial statementsRun
        simp only [lowerBlockValue] at valueRun
        rw [← sameEnv] at valueRun
        have resultTyped := lowerExpr_generated_typed expr source valueRun valueLive statementsGenerated
        have retained := types_emitEffect (.leave scope) _ _ _ _ leaveRun result (.data type) resultTyped
        exact types_popScope _ _ _ _ popRun result (.data type) retained

theorem lowerContext_tail_values_of_accepted {module : Core.Module} {context : Context} {impl : Core.Impl}
    (accepted : Core.validate module = .ok ()) {contextIndex : Nat}
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    (pre : List (SlotId × ValueId × OriginId)) (want : Bool)
    {before after : LS} {value : ValueId}
    (run : lowerBlock none pre want impl.body (lowerEnv module impl.vars impl.results.toList) before = (value, after))
    (live : after.cur.isSome = true) (generated : GeneratedBuilderState before)
    (tail : impl.body.value.isSome = true) : TypedValues after impl.results.toList [value] := by
  obtain ⟨type, finish, source, results⟩ := accepted_context_tail_result accepted contextAt implAt tail
  have typed := lowerBlock_tail_generated_typed impl.body source tail pre want run live generated
  rw [results]
  exact .cons typed .nil

theorem accepted_implementation_no_tail {module : Core.Module} {impl : Core.Impl}
    (accepted : Core.validate module = .ok ()) {index : ImplId}
    (implAt : module.impls[index]? = some impl)
    (noValue : impl.body.value.isNone = true) :
    impl.results.isEmpty = true ∨ impl.body.diverges module.noReturn = true := by
  obtain ⟨type, finish, source, shape⟩ := ((validate_modOk module accepted).impl index impl implAt).body
  rcases shape with ⟨empty, _⟩ | ⟨result, results, _, diverges⟩
  · left
    simpa using List.isEmpty_iff.mpr empty
  · right
    apply diverges
    cases value : impl.body.value <;> simp_all

end Goose.Lower.Validation
