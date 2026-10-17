import Goose.Lower.Validation.ReplacementContentFlowSourceReadyCallTypes
import Goose.Core.Sound.Invert

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.typedCall {module : GIR.Module} {callees : Array State} {func callee : Func}
    {moduleTypes : Array (Array (Option VTy))} {types calleeTypes : Array (Option VTy)}
    {state effects : State} {completed before : LS} {calleeProvenance : Prov}
    {typingEnv : TEnv} {index : ContextId} {syntaxArgs : List Arg} {origin : OriginId}
    {type : Ty} {startOffset finishOffset : Nat} {results : List Ty}
    {ctx : Core.Context} {implementation : Core.Impl}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyExpr typingEnv (.call index syntaxArgs origin) startOffset = .ok (type, finishOffset))
    (sourceContext : typingEnv.mod.contexts[index]? = some ctx)
    (sourceImpl : typingEnv.mod.impls[ctx.impl]? = some implementation)
    (resultRows : callee.results = implementation.results.toList)
    (closed : close module moduleTypes = some callees)
    (calleeRow : module.funcs[index]? = some callee) (effectRow : callees[index]? = some effects)
    (canonical : effects.CanonicalWithin callee calleeTypes calleeProvenance)
    (parameters : ∀ parameter root, root ∈ callee.parameterRoots parameter →
      root = .param parameter ∨ ∃ global, root = .global global)
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerExpr (.call index syntaxArgs origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (arguments : ValuesReadyAt state (lowerArgs syntaxArgs) (lowerEnv typingEnv.mod typingEnv.vars results) before)
    (extension : (lowerExpr (.call index syntaxArgs origin)
      (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerExpr (.call index syntaxArgs origin)
      (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (contents :
      let lowered := lowerArgs syntaxArgs (lowerEnv typingEnv.mod typingEnv.vars results) before
      lowered.2.cur.isSome = true → ∀ position argument,
        (callee.roots.contents.find? (·.1 == position)).isSome = true →
        lowered.1[position]? = some argument → content func state (flowAt state.values argument) ≠ .pending) :
    ValueReadyAt state (lowerExpr (.call index syntaxArgs origin))
      (lowerEnv typingEnv.mod typingEnv.vars results) before := by
  apply frame.callExpression closed calleeRow effectRow canonical parameters generated.live
    arguments extension allocated ?_ contents
  dsimp only
  intro live
  have tag := source_call_emitted_type source generated native live
  obtain ⟨actualContext, actualImpl, argsStart, argsFinish, resultStart, contextRow, implRow,
    _, _, resultTyped⟩ := tyExpr_call_tables source
  have sameContext := Option.some.inj (sourceContext.symm.trans contextRow)
  subst actualContext
  have sameImpl := Option.some.inj (sourceImpl.symm.trans implRow)
  subst actualImpl
  rcases ((callResultTy_ok implementation resultStart (type, finishOffset)).mp resultTyped).1 with
    ⟨empty, unit⟩ | single
  · have typeUnit : type = .unit := unit
    rw [typeUnit] at tag
    exact Or.inl ⟨resultRows.trans empty, tag⟩
  · exact Or.inr ⟨type, resultRows.trans single, tag⟩

#print axioms SourceReadyFrame.typedCall

end Goose.Lower.Validation.ReplacementContentFlowSource
