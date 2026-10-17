import Goose.Lower.Validation.ReplacementContentFlowSourceReadyCallExpressions
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem source_call_emitted_type {typingEnv : TEnv} {index : ContextId} {syntaxArgs : List Arg}
    {origin : OriginId} {type : Ty} {start finish : Nat} {results : List Ty} {before : LS}
    {types : Array (Option VTy)}
    (source : Core.tyExpr typingEnv (.call index syntaxArgs origin) start = .ok (type, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerExpr (.call index syntaxArgs origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2) :
    let env := lowerEnv typingEnv.mod typingEnv.vars results
    let arguments := lowerArgs syntaxArgs env before
    let called := Lower.emitDef (.call index arguments.1 (some origin)) env arguments.2
    arguments.2.cur.isSome = true → types[called.1]? = some (some (.data type)) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let arguments := lowerArgs syntaxArgs env before
  let called := Lower.emitDef (.call index arguments.1 (some origin)) env arguments.2
  change arguments.2.cur.isSome = true → types[called.1]? = some (some (.data type))
  intro live
  obtain ⟨ctx, implementation, argsStart, argsFinish, resultStart, contextRow, implRow,
    arity, argumentsTyped, resultTyped⟩ := tyExpr_call_tables source
  have passable := lowerArgs_generated_typed syntaxArgs arity argumentsTyped
    (show lowerArgs syntaxArgs env before = arguments from rfl) live generated
  have signature : env.sigs[index]? = some
      (implementation.params.toList.map (fun parameter => tyOfVar implementation parameter.var),
        implementation.results.toList) := by
    simp [env, lowerEnv, Array.getElem?_map, contextRow, implRow]
  have operation := call_resultTy_of_passable signature passable resultTyped origin
  cases current : arguments.2.cur with
  | none => simp [current] at live
  | some block =>
    have cached : called.2.vals[called.1]? = some (some (.data type)) :=
      (emitDef_recorded current operation).2.2.1
    have retained : TypePrefix called.2
        (lowerExpr (.call index syntaxArgs origin) env before).2 := by
      have run : lowerExpr (.call index syntaxArgs origin) env before =
          (called.1, if env.mod.noReturn index then
            (Lower.emitTerm .unreachable env called.2).2 else called.2) := by
        cases noReturn : env.mod.noReturn index <;>
          simp [lowerExpr, bind_run, read, noReturn, arguments, called, pure_run]
      rw [run]
      cases noReturn : env.mod.noReturn index with
      | false =>
        simpa only [noReturn, Bool.false_eq_true, ↓reduceIte] using (TypePrefix.refl called.2)
      | true =>
        simp only [↓reduceIte]
        exact types_emitTerm .unreachable env called.2 _ _ rfl
    exact native called.1 (.data type) (retained _ _ cached)

#print axioms source_call_emitted_type

end Goose.Lower.Validation.ReplacementContentFlowSource
