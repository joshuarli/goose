import Goose.Lower.DemandSliceAssignmentSequence
import Goose.Lower.DemandWhileMixedStatements
import Goose.Lower.DemandIfMixedSequence
import Goose.Lower.DemandWhileMixedTerminal
import Goose.Lower.DemandScalarAssignmentStatementsNormal

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive SliceMixedStatements (cfg : Cfg) (env : Env) : List Stmt → Prop
  | mixed {statements : List Stmt} (fragment : WhileMixedStatements cfg env statements) :
      SliceMixedStatements cfg env statements
  | control {earlier later : List Stmt} (fragment : WhileMixedStatements cfg env earlier)
      (tail : SliceMixedStatements cfg env later) : SliceMixedStatements cfg env (earlier ++ later)
  | assignment (reference : Expr) (mutability : Mutability) (global : GlobalId) (intType : IntTy) (number : Int)
      (sliceOrigin origin : OriginId) {rest : List Stmt} (tail : SliceMixedStatements cfg env rest) :
      SliceMixedStatements cfg env (.assign (.deref reference)
        (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin :: rest)

inductive SliceMixedCursor {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | mixed {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : WhileMixedStatementCursor cx results selected source before built initial start map required runtime) :
      SliceMixedCursor cx results selected source before built initial start map required runtime
  | slice {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : SliceAssignmentCursor cx results source before built initial start map required runtime) :
      SliceMixedCursor cx results selected source before built initial start map required runtime

theorem accepted_generated_slice_mixed_statements {cfg : Cfg} {env : Env} {statements : List Stmt}
    (fragment : SliceMixedStatements cfg env statements) :
    ∀ {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
      (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
      (before : LS) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block),
      GeneratedSequencePrefixFamily cx results selected before none bindings want block statements
        (@SliceMixedCursor cfg env cx results root owner selected) ∧
      GeneratedStoppedSequencePrefixFamily cx results selected before none bindings want block statements := by
  induction fragment with
  | mixed fragment =>
    intro cx results root owner selected before bindings want block
    obtain ⟨family, stopped⟩ := accepted_generated_while_mixed_statements fragment selected before bindings want block
    exact ⟨family.mapCursor (by intro statement state source before built initial start map required runtime cursor; exact .mixed cursor), stopped⟩
  | @control earlier later fragment tail ih =>
    intro cx results root owner selected before bindings want block
    obtain ⟨family, stopped⟩ := ih selected before bindings want block
    have tailFamilies : InvariantSequencePrefixFamily cx results selected before none bindings want block later
        (@SliceMixedCursor cfg env cx results root owner selected) (fun _ => True) ∧
      InvariantStoppedSequencePrefixFamily cx results selected before none bindings want block later (fun _ => True) := by
      constructor
      · intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps
        exact family source owned occurrence all scope value rows coverage admitted bounded realized input extended steps
      · intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps fuel stop after targetStop nonTimeout
        exact stopped source owned occurrence all scope value rows coverage admitted bounded realized input extended steps targetStop nonTimeout
    have combined := accepted_generated_invariant_while_mixed_prepend fragment selected before bindings want block
      (@SliceMixedCursor cfg env cx results root owner selected) (by
        intro statement state source before built initial start map required runtime cursor
        exact .mixed cursor) (fun _ => True) (fun _ _ => trivial) tailFamilies
    constructor
    · intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended taken reached steps
      exact combined.1 source owned occurrence all scope value rows coverage admitted bounded realized input extended trivial steps
    · intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended taken reached steps fuel stop after targetStop nonTimeout
      exact combined.2 source owned occurrence all scope value rows coverage admitted bounded realized input extended trivial steps targetStop nonTimeout
  | assignment reference mutability global intType number sliceOrigin origin tail ih =>
    intro cx results root owner selected before bindings want block
    obtain ⟨family, stopped⟩ := ih selected before bindings want block
    have head : GeneratedStatementPrefixFamily cx results selected none (.assign (.deref reference)
        (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin)
        (@SliceMixedCursor cfg env cx results root owner selected) :=
      GeneratedStatementPrefixFamily.mapCursor
        (selected := selected) (loop := none)
        (accepted_generated_slice_assignment_prefix_family selected none reference mutability global intType number sliceOrigin origin)
        (by intro statement state source before built initial start map required runtime cursor; exact .slice cursor)
    exact ⟨accepted_generated_sequence_prefix_cons selected before none bindings want block _ head family,
      accepted_generated_stopped_sequence_cons selected before none bindings want block
        (accepted_generated_slice_assignment_accepted_stopped_family selected none reference mutability global intType number sliceOrigin origin) stopped⟩

theorem normal_after_fragment {cfg : Cfg} {env : Env} {earlier later : List Stmt}
    (valid : stmtsOk earlier = true)
    (tailNormal : ∀ {fuel : Nat} {state after : St} {flow : Flow},
      execStmts fuel cfg env later state = .ok flow after → flow = .normal .unit)
    {fuel : Nat} {state after : St} {flow : Flow}
    (done : execStmts fuel cfg env (earlier ++ later) state = .ok flow after) : flow = .normal .unit := by
  induction earlier generalizing fuel state after flow with
  | nil => exact tailNormal done
  | cons head tail ih =>
    cases fuel with
    | zero => simp [execStmts, timeout, M.stop] at done
    | succ fuel =>
      simp only [stmtsOk, Bool.and_eq_true] at valid
      simp only [List.cons_append, execStmts, bind_apply] at done
      cases executed : execStmt fuel cfg env head state with
      | stop stop final => simp only [executed] at done; cases done
      | ok headFlow middle =>
        have normal := execStmt_fragment_normal fuel cfg env head valid.1 state middle headFlow executed
        subst headFlow
        simp only [executed] at done
        exact ih valid.2 done

theorem SliceMixedStatements.normal {cfg : Cfg} {env : Env} {statements : List Stmt}
    (fragment : SliceMixedStatements cfg env statements) {fuel : Nat} {state after : St} {flow : Flow}
    (done : execStmts fuel cfg env statements state = .ok flow after) : flow = .normal .unit := by
  induction fragment generalizing fuel state after flow with
  | mixed fragment => exact fragment.normal done
  | control fragment tail ih => exact normal_after_fragment fragment.fragment (fun run => ih run) done
  | assignment reference mutability global intType number sliceOrigin origin tail ih =>
    cases fuel with
    | zero => simp [execStmts, timeout, M.stop] at done
    | succ fuel =>
      simp only [execStmts, bind_apply] at done
      cases head : execStmt fuel cfg env (.assign (.deref reference)
          (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin) state with
      | stop stop final => simp only [head] at done; cases done
      | ok headFlow middle =>
        have normal := assignment_normal head
        subst headFlow
        simp only [head] at done
        exact ih done

#print axioms SliceMixedStatements.normal

theorem SliceMixedCursor.excludes_maximal_terminal {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : SliceMixedCursor cx results selected source before built initial start map required runtime)
    {term : Term} (terminal : instAt cx.fn runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep cx fuel runtime next) : False := by
  cases cursor with
  | mixed cursor => exact cursor.excludes_maximal_terminal terminal maximal
  | slice cursor =>
    rcases cursor.nonterminal with ⟨id, op, found⟩ | ⟨effect, found⟩ <;> cases found.symm.trans terminal

#print axioms SliceMixedCursor.excludes_maximal_terminal

#print axioms accepted_generated_slice_mixed_statements
end Goose.Lower
