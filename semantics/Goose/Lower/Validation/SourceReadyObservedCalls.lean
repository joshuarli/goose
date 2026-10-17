import Goose.Lower.Validation.SourceReadyCallObservations
import Goose.Lower.Validation.SourceReadyCallFrames

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFunction.call_with_observations (facts : SourceReadyFunction)
    {typingEnv : TEnv} {index : ContextId} {syntaxArgs : List Arg} {origin : OriginId}
    {type : Ty} {start finish : Nat} {results : List Ty} {before : LS}
    (tables : SourceRootTables typingEnv facts.source)
    (source : Core.tyExpr typingEnv (.call index syntaxArgs origin) start = .ok (type, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows facts.types
      (lowerExpr (.call index syntaxArgs origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerExpr (.call index syntaxArgs origin)
      (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext facts.completed)
    (allocated : (lowerExpr (.call index syntaxArgs origin)
      (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ facts.completed.vals.size)
    (visible : VisibleSlotsReady typingEnv facts.state)
    (argumentsChild : ∀ implementation argsStart argsFinish,
      Core.tyArgs typingEnv implementation implementation.params.toList syntaxArgs argsStart = .ok ((), argsFinish) →
      implementation.params.toList.length = syntaxArgs.length →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows facts.types
        (lowerArgs syntaxArgs (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerArgs syntaxArgs (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext facts.completed →
      (lowerArgs syntaxArgs (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ facts.completed.vals.size →
      VisibleSlotsReady typingEnv facts.state →
      ValuesReadyAt facts.state (lowerArgs syntaxArgs) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
        EmitsOnly (ReadyCallObservations (lower facts.source.mod) facts.func facts.state) before
          (lowerArgs syntaxArgs (lowerEnv typingEnv.mod typingEnv.vars results) before).2) :
    ValueReadyAt facts.state (lowerExpr (.call index syntaxArgs origin)) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations (lower facts.source.mod) facts.func facts.state) before
        (lowerExpr (.call index syntaxArgs origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  obtain ⟨ctx, implementation, argsStart, argsFinish, resultStart, contextRow, implementationRow,
    arity, argumentsTyped, resultTyped⟩ := tyExpr_call_tables source
  have sourceContext : facts.source.mod.contexts[index]? = some ctx := by
    simpa only [tables.moduleEq] using contextRow
  have sourceImplementation : facts.source.mod.impls[ctx.impl]? = some implementation := by
    simpa only [tables.moduleEq] using implementationRow
  let callee := lowerContextAt facts.source.mod ctx implementation
  have calleeRow : (lower facts.source.mod).funcs[index]? = some callee :=
    lower_func_at sourceContext sourceImplementation
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let arguments := lowerArgs syntaxArgs env before
  let called := Lower.emitDef (.call index arguments.1 (some origin)) env arguments.2
  have tailAdvance := call_emission_advance index syntaxArgs origin env before
  have tailTypes := call_emission_types index syntaxArgs origin env before
  have callAdvance : arguments.2.Adv called.2 := adv_emitDef
    (show Lower.emitDef (.call index arguments.1 (some origin)) env arguments.2 = called from rfl)
  have argumentExtension := callAdvance.ext.trans (tailAdvance.ext.trans extension)
  have argumentAllocated := Nat.le_trans callAdvance.vals (Nat.le_trans tailAdvance.vals allocated)
  have argumentNative : SummaryPreservation.NativeRows facts.types arguments.2 :=
    (native.of_prefix tailTypes).of_prefix (types_emitDef (.call index arguments.1 (some origin)) env arguments.2 _ _ rfl)
  have argumentsProof := argumentsChild implementation argsStart argsFinish argumentsTyped arity
    generated argumentNative argumentExtension argumentAllocated visible
  have ready := facts.call tables source generated native extension allocated visible
    (fun _ _ _ _ _ _ _ _ _ _ => argumentsProof.1)
  refine ⟨ready, argumentsProof.2.trans (?_ : EmitsOnly _ arguments.2 called.2) |>.trans ?_⟩
  · cases current : arguments.2.cur with
    | none =>
      apply EmitsOnly.of_blocks
      simp only [called, emitDef_none _ _ current]
    | some block =>
      have live : arguments.2.cur.isSome = true := by simp [current]
      obtain ⟨body, member, instruction⟩ := emitted_definition_retained current
        ((generated.lowerArgs syntaxArgs rfl).live block current)
        (show Lower.emitDef (.call index arguments.1 (some origin)) env arguments.2 = called from rfl)
        (tailAdvance.ext.trans extension) facts.frame.blocks
      obtain ⟨site⟩ := facts.native.calls body member called.1 index arguments.1 (some origin) instruction
      have sameCallee : site.callee = callee := Option.some.inj (site.calleeAt.symm.trans calleeRow)
      have occurrence := (facts.occurrences body member _ instruction).2.2.1 called.1 index arguments.1 (some origin) rfl
      have contents := facts.call_contents tables sourceContext sourceImplementation argumentsTyped arity
        generated argumentNative argumentExtension argumentAllocated visible argumentsProof.1 occurrence live
      have observation := facts.call_observation site
        (facts.moduleFacts.functions index site.callee site.calleeAt).roots
        (fun selected value row => argumentsProof.1.2 live value (List.mem_of_getElem? row)) (by
          intro selected value observed row
          exact contents selected value (by simpa only [sameCallee] using observed) row)
      apply emitsOnly_emitDef (show Lower.emitDef (.call index arguments.1 (some origin)) env arguments.2 = called from rfl)
      apply ReadyCallObservations.call
      intro actual actualRow
      have same : actual = site.callee := Option.some.inj (actualRow.symm.trans site.calleeAt)
      simpa only [same] using observation
  · rw [lower_call_run]
    cases noReturn : env.mod.noReturn index with
    | false => simp only [Bool.false_eq_true, reduceIte]; exact EmitsOnly.refl _ _
    | true =>
      simp only [reduceIte]
      exact emitsOnly_emitTerm .unreachable (.term _ _ _ _) env called.2 _ _ rfl

#print axioms SourceReadyFunction.call_with_observations

end Goose.Lower.Validation.ReplacementContentFlowSource
