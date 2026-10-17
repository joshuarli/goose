import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceScalarsBasic
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes
import Goose.Lower.Validation.SourceRootShapeReads

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem sourceExpressionNative {typingEnv : TEnv} {env : PEnv} {types : Array (Option VTy)}
    {expression : Expr} {type : Ty} {start finish : Nat} {results : List Ty}
    {before after : LS} {value : ValueId}
    (tables : SourceRootTables typingEnv env) (native : NativeRows types after)
    (generated : GeneratedBuilderState before)
    (source : Core.tyExpr typingEnv expression start = .ok (type, finish))
    (run : lowerExpr expression (lowerEnv env.mod env.impl.vars results) before = (value, after))
    (live : after.cur.isSome = true) : types[value]? = some (some (.data type)) := by
  apply native.expression generated source
  · simpa only [tables.moduleEq, tables.variablesEq] using run
  · exact live

theorem nativeFlat_not_reference {types : Array (Option VTy)} {value : ValueId} {type : Ty}
    (row : types[value]? = some (some (.data type))) (flat : type.flat = true)
    (mutability : Mutability) (payload : Ty) :
    types[value]? ≠ some (some (.data (.ref mutability payload))) := by
  intro reference
  rw [row] at reference
  cases reference
  cases flat

#print axioms sourceExpressionNative
#print axioms nativeFlat_not_reference

end Goose.Lower.Validation.ReplacementContentFlowSource
