import Goose.Lower.Validation.SourceReadyCallFrames
import Goose.Lower.Validation.SourceReadyCallContents

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFunction.call (facts : SourceReadyFunction)
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
      ValuesReadyAt facts.state (lowerArgs syntaxArgs) (lowerEnv typingEnv.mod typingEnv.vars results) before) :
    ValueReadyAt facts.state (lowerExpr (.call index syntaxArgs origin))
      (lowerEnv typingEnv.mod typingEnv.vars results) before := by
  obtain ⟨ctx, implementation, argsStart, argsFinish, resultStart, contextRow, implementationRow,
    arity, argumentsTyped, resultTyped⟩ := tyExpr_call_tables source
  have sourceContext : facts.source.mod.contexts[index]? = some ctx := by
    simpa only [tables.moduleEq] using contextRow
  have sourceImplementation : facts.source.mod.impls[ctx.impl]? = some implementation := by
    simpa only [tables.moduleEq] using implementationRow
  let callee := lowerContextAt facts.source.mod ctx implementation
  have calleeRow : (lower facts.source.mod).funcs[index]? = some callee :=
    lower_func_at sourceContext sourceImplementation
  obtain ⟨effects, effectRow, effectBounds⟩ := facts.moduleBounds.2 index callee calleeRow
  have calleeFacts := facts.moduleFacts.functions index callee calleeRow
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let arguments := lowerArgs syntaxArgs env before
  let called := Lower.emitDef (.call index arguments.1 (some origin)) env arguments.2
  have tailAdvance := call_emission_advance index syntaxArgs origin env before
  have tailTypes := call_emission_types index syntaxArgs origin env before
  have callAdvance : arguments.2.Adv called.2 := adv_emitDef (show Lower.emitDef (.call index arguments.1 (some origin)) env arguments.2 = called from rfl)
  have argumentExtension : arguments.2.Ext facts.completed :=
    callAdvance.ext.trans (tailAdvance.ext.trans extension)
  have argumentAllocated : arguments.2.vals.size ≤ facts.completed.vals.size :=
    Nat.le_trans callAdvance.vals (Nat.le_trans tailAdvance.vals allocated)
  have argumentNative : SummaryPreservation.NativeRows facts.types arguments.2 :=
    (native.of_prefix tailTypes).of_prefix (types_emitDef (.call index arguments.1 (some origin)) env arguments.2 _ _ rfl)
  have argumentsReady := argumentsChild implementation argsStart argsFinish argumentsTyped arity
    generated argumentNative argumentExtension argumentAllocated visible
  apply facts.frame.typedCall source contextRow implementationRow
    (show callee.results = implementation.results.toList from rfl) facts.closed calleeRow effectRow
    effectBounds calleeFacts.roots.closed generated native argumentsReady extension allocated
  dsimp only
  intro live
  have occurrence := facts.emittedCall
    (show Lower.emitDef (.call index arguments.1 (some origin)) env arguments.2 = called from rfl)
    (generated.lowerArgs syntaxArgs rfl).live live (tailAdvance.ext.trans extension)
  exact facts.call_contents tables sourceContext sourceImplementation argumentsTyped arity generated
    argumentNative argumentExtension argumentAllocated visible argumentsReady occurrence live

#print axioms SourceReadyFunction.call

end Goose.Lower.Validation.ReplacementContentFlowSource
