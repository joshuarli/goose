import Goose.Lower.Validation.SummaryPreservationReturnBounds
import Goose.Lower.Validation.SummaryPreservationReturnFrames
import Goose.Lower.GeneratedBuilder

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

namespace BuilderReturnsBound

variable {before after : LS} {oldUpper newUpper : Prov} {target : List RootRef}
  {le : LEnv} {scopeCount : Nat}

theorem frame (prior : BuilderReturnsBound oldUpper target before)
    (symbols : before.SymbolWF le scopeCount) (size : oldUpper.vals.size = before.vals.size)
    (retained : ∀ index, index < oldUpper.vals.size → rootsAt newUpper.vals index = rootsAt oldUpper.vals index)
    (returns : ReturnMembershipFrame before after) : BuilderReturnsBound newUpper target after :=
  prior.retained symbols size retained (fun value origin => returns [value] origin)

theorem expression {env : TEnv} {expression : Expr} {type : Ty} {start finish : Nat} {value : ValueId}
    (prior : BuilderReturnsBound oldUpper target before)
    (symbols : before.SymbolWF le scopeCount) (size : oldUpper.vals.size = before.vals.size)
    (source : Core.tyExpr env expression start = .ok (type, finish))
    (run : lowerExpr expression le before = (value, after))
    (retained : ∀ index, index < oldUpper.vals.size → rootsAt newUpper.vals index = rootsAt oldUpper.vals index) :
    BuilderReturnsBound newUpper target after :=
  prior.frame symbols size retained (source_expression_return_frame source le before value after run)

theorem place {env : TEnv} {place : Place} {info : PlaceInfo} {start finish : Nat} {value : ValueId}
    (prior : BuilderReturnsBound oldUpper target before)
    (symbols : before.SymbolWF le scopeCount) (size : oldUpper.vals.size = before.vals.size)
    (source : Core.tyPlace env place start = .ok (info, finish))
    (run : lowerPlace place le before = (value, after))
    (retained : ∀ index, index < oldUpper.vals.size → rootsAt newUpper.vals index = rootsAt oldUpper.vals index) :
    BuilderReturnsBound newUpper target after :=
  prior.frame symbols size retained (source_place_return_frame source le before value after run)

theorem view {env : TEnv} {view : View} {info : Ty × Bool} {start finish : Nat} {value : ValueId}
    (prior : BuilderReturnsBound oldUpper target before)
    (symbols : before.SymbolWF le scopeCount) (size : oldUpper.vals.size = before.vals.size)
    (source : Core.tyView env view start = .ok (info, finish))
    (run : lowerView view le before = (value, after))
    (retained : ∀ index, index < oldUpper.vals.size → rootsAt newUpper.vals index = rootsAt oldUpper.vals index) :
    BuilderReturnsBound newUpper target after :=
  prior.frame symbols size retained (source_view_return_frame source le before value after run)

theorem arguments {env : TEnv} {args : List Arg} {params : List Param} {callee : Impl}
    {start finish : Nat} {values : List ValueId}
    (prior : BuilderReturnsBound oldUpper target before)
    (symbols : before.SymbolWF le scopeCount) (size : oldUpper.vals.size = before.vals.size)
    (source : Core.tyArgs env callee params args start = .ok ((), finish))
    (arity : params.length = args.length)
    (run : lowerArgs args le before = (values, after))
    (retained : ∀ index, index < oldUpper.vals.size → rootsAt newUpper.vals index = rootsAt oldUpper.vals index) :
    BuilderReturnsBound newUpper target after :=
  prior.frame symbols size retained
    (returnFrame_lowerArgs args (tyArgs_returnFree args params source arity) le before values after run)

private theorem leaveAll_current (scopes : List ScopeId) (le : LEnv) (state : LS) :
    (Goose.Lower.leaveAll scopes le state).2.cur = state.cur := by
  induction scopes generalizing state with
  | nil => rfl
  | cons scope rest ih =>
    simp only [Goose.Lower.leaveAll, bind_run]
    rw [ih]
    cases current : state.cur with
    | none => rw [emitEffect_none _ _ current]; exact current
    | some block => rw [emitEffect_run _ _ current]; exact current

private theorem leaveTo_current (depth : Nat) (le : LEnv) (state : LS) :
    (Goose.Lower.leaveTo depth le state).2.cur = state.cur := by
  simpa only [Goose.Lower.leaveTo, bind_run, get_apply] using leaveAll_current _ le state

theorem returned_expression {env : TEnv} {expression : Expr} {type : Ty} {start finish : Nat}
    {value returned : ValueId} {expressionState returnedState : LS} {origin : OriginId}
    (loop : Option LoopCtx)
    (prior : BuilderReturnsBound oldUpper target before)
    (symbols : before.SymbolWF le scopeCount) (size : oldUpper.vals.size = before.vals.size)
    (generated : GeneratedBuilderState before)
    (source : Core.tyExpr env expression start = .ok (type, finish))
    (expressionRun : lowerExpr expression le before = (value, expressionState))
    (coercedRun : Goose.Lower.coerceResult value origin le expressionState = (returned, returnedState))
    (retained : ∀ index, index < oldUpper.vals.size → rootsAt newUpper.vals index = rootsAt oldUpper.vals index)
    (candidate : returnedState.cur.isSome = true → ∀ root ∈ rootsAt newUpper.vals returned, root ∈ target) :
    BuilderReturnsBound newUpper target (lowerStmt loop (.ret (some expression) origin) le before).2 := by
  let left := (Goose.Lower.leaveTo 0 le returnedState).2
  have expressionFrame := source_expression_return_frame source le before value expressionState expressionRun
  have coerceFrame := ReturnFrameRun.of_absence (fun _ => ReturnFrames.returnAbsent_coerceResult value origin)
    le expressionState returned returnedState coercedRun
  have leaveFrame := ReturnFrameRun.of_absence (fun _ => ReturnFrames.returnAbsent_leaveTo 0)
    le returnedState () left rfl
  have priorLeft : BuilderReturnsBound newUpper target left :=
    prior.frame symbols size retained (expressionFrame.trans (coerceFrame.trans leaveFrame))
  have expressionGenerated := generated.lowerExpr expression expressionRun
  have returnedGenerated := expressionGenerated.coerceResult value origin coercedRun
  have leftGenerated : GeneratedBuilderState left := returnedGenerated.leaveTo 0 rfl
  have whole : lowerStmt loop (.ret (some expression) origin) le before =
      Goose.Lower.emitTerm (.ret [returned] (some origin)) le left := by
    simp only [lowerStmt, bind_run, expressionRun, coercedRun, pure_run, left]
  rw [whole]
  cases current : returnedState.cur with
  | none =>
    have stopped : left.cur = none := (leaveTo_current 0 le returnedState).trans current
    rw [emitTerm_none _ _ stopped]
    exact priorLeft
  | some block =>
    apply priorLeft.emitTerm leftGenerated.live (.ret [returned] (some origin))
    intro found foundOrigin same
    have pair := Term.ret.inj same
    have valueSame : found = returned := by simpa using pair.1.symm
    subst found
    exact candidate (by simp [current])

#print axioms frame
#print axioms expression
#print axioms place
#print axioms view
#print axioms arguments
#print axioms returned_expression

end BuilderReturnsBound

end Goose.Lower.Validation.SummaryPreservation
