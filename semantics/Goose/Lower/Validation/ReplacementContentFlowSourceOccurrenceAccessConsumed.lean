import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessKernel
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceScalarsConsumed

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem nativeScalar_not_reference {types : Array (Option VTy)} {value : ValueId}
    (scalar : valRefLike types value = false) (mutability : Mutability) (payload : Ty) :
    types[value]? ≠ some (some (.data (.ref mutability payload))) := by
  intro row
  simp only [valRefLike, row, VTy.refLike, Ty.isRefLike] at scalar
  cases scalar

theorem nativeData_not_reference {types : Array (Option VTy)} {value : ValueId} {type : Ty}
    (row : types[value]? = some (some (.data type)))
    (nonreference : ∀ mutability payload, type ≠ .ref mutability payload)
    (mutability : Mutability) (payload : Ty) :
    types[value]? ≠ some (some (.data (.ref mutability payload))) := by
  intro reference
  rw [row] at reference
  cases reference
  exact nonreference _ _ rfl

theorem sourceView_not_reference {typingEnv : TEnv} {env : PEnv} {types : Array (Option VTy)}
    {view : View} {info : Ty × Bool} {start finish : Nat} {results : List Ty}
    {before after : LS} {value : ValueId}
    (tables : SourceRootTables typingEnv env) (native : NativeRows types after)
    (generated : GeneratedBuilderState before)
    (source : Core.tyView typingEnv view start = .ok (info, finish))
    (run : lowerView view (lowerEnv env.mod env.impl.vars results) before = (value, after))
    (live : after.cur.isSome = true) (mutability : Mutability) (payload : Ty) :
    types[value]? ≠ some (some (.data (.ref mutability payload))) := by
  obtain ⟨viewMutability, row⟩ := native.view generated source
    (by simpa only [tables.moduleEq, tables.variablesEq] using run) live
  intro reference
  rw [row] at reference
  cases reference

theorem sourceValueView_not_reference {env : TEnv} {expression : Expr} {start finish : Nat}
    {info : Ty × Bool} {childType : Ty} {childFinish : Nat}
    (source : Core.tyView env (.val expression) start = .ok (info, finish))
    (child : Core.tyExpr env expression start = .ok (childType, childFinish)) :
    ∀ mutability payload, childType ≠ .ref mutability payload := by
  simp only [Core.tyView, child, bind, StateT.bind, Except.bind] at source
  cases childType
  case ref => exact False.elim ((rej_ok _ _ _ _).mp source)
  all_goals exact fun _ _ same => by cases same

#print axioms nativeScalar_not_reference
#print axioms sourceView_not_reference
#print axioms sourceValueView_not_reference

end Goose.Lower.Validation.ReplacementContentFlowSource
