import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsActions
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts
import Goose.Lower.Validation.SummaryPreservationSourceMutationKernelsCommon

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem occurrence_owner_element_flat {type element : Ty}
    (allowed : type.paramOk = true) (owner : type.ownerElem? = some element) :
    element.flat = true := by
  cases type <;> simp_all [Ty.paramOk, Ty.storable, Ty.isRefSlice, Ty.ownerElem?]

theorem occurrence_mutation_transfer {typingEnv output : TEnv} {env : PEnv}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty}
    {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat}
    {initial : LS} {upper next : Prov} {scope start finish : Nat} {statement : Stmt}
    {expected : List RootRef} (loop : Option LoopCtx)
    (typed : tyStmt typingEnv scope statement start = .ok (output, finish)) (plain : statement.isPlain = true)
    (ready : ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount slots initial upper)
    (retained : ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) :
    ReturnBoundsPreserved expected initial upper
      (lowerStmt loop statement (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next :=
  ReturnBoundsPreserved.frame ready.symbols ready.roots.valueSize retained
    (returnFrame_lowerStmt loop statement (tyStmt_returnFree_of_plain_or_inExpr statement typed (Or.inr plain)) _ _ _ _ rfl)

theorem _root_.Goose.Lower.Validation.SourceRootTables.occurrence_native_place_row
    {typingEnv : TEnv} {env : PEnv} {returnTypes : List Ty} {vt : Array (Option VTy)}
    {place : Place} {info : PlaceInfo} {start finish : Nat} {before after : LS} {value : ValueId}
    (tables : SourceRootTables typingEnv env) (native : NativeRows vt after)
    (generated : GeneratedBuilderState before) (typed : tyPlace typingEnv place start = .ok (info, finish))
    (run : lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) before = (value, after))
    (live : after.cur.isSome = true) : ∃ mutability, vt[value]? = some (some (.data (.ref mutability info.ty))) := by
  apply native.place (results := returnTypes) generated typed _ live
  simpa only [← tables.moduleEq, ← tables.variablesEq] using run

theorem _root_.Goose.Lower.Validation.SourceRootTables.occurrence_native_expression_row
    {typingEnv : TEnv} {env : PEnv} {returnTypes : List Ty} {vt : Array (Option VTy)}
    {expression : Expr} {type : Ty} {start finish : Nat} {before after : LS} {value : ValueId}
    (tables : SourceRootTables typingEnv env) (native : NativeRows vt after)
    (generated : GeneratedBuilderState before) (typed : tyExpr typingEnv expression start = .ok (type, finish))
    (run : lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) before = (value, after))
    (live : after.cur.isSome = true) : vt[value]? = some (some (.data type)) := by
  apply native.expression (results := returnTypes) generated typed _ live
  simpa only [← tables.moduleEq, ← tables.variablesEq] using run

end Goose.Lower.Validation.ReplacementContentFlowSource
