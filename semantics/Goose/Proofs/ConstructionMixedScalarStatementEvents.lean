import Goose.Proofs.ConstructionMixedScalarValueEvents
import Goose.Proofs.ConstructionFreshByteBindingEvents

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionProtocol

def KeepsConstructionEvents (action : EvalM α) : Prop :=
  ∀ state, (Goose.Proofs.Exit.stepState (action state)).construction.events = state.construction.events

theorem KeepsConstructionEvents.query (action : EvalM α) (query : StateQuery action) : KeepsConstructionEvents action := by
  intro state
  rw [query state]

theorem KeepsConstructionEvents.bind (action : EvalM α) (next : α → EvalM β)
    (first : KeepsConstructionEvents action) (rest : ∀ value, KeepsConstructionEvents (next value)) :
    KeepsConstructionEvents (action >>= next) := by
  intro state
  rw [bind_events_frame action next state rest]
  exact first state

theorem KeepsConstructionEvents.pure (value : α) : KeepsConstructionEvents (pure value) :=
  KeepsConstructionEvents.query _ (stateQuery_pure value)

theorem KeepsConstructionEvents.stop (reason : Goose.Core.Stop) : KeepsConstructionEvents (EvalM.stop (α := α) reason) :=
  KeepsConstructionEvents.query _ (stateQuery_stop reason)

theorem writeLoc_direct_events (fuel : Nat) (layout : LayoutEnv) (root : Goose.Core.RootInst) (value : Value) :
    KeepsConstructionEvents (writeLoc fuel layout ⟨root, []⟩ value) := by
  intro state
  cases found : state.objects.lookup root with
  | none => simp [writeLoc, EvalM.get, bind, found, fault, EvalM.stop, Goose.Proofs.Exit.stepState]
  | some old =>
    cases fuel with
    | zero => simp [writeLoc, EvalM.get, bind, found, writeValuePath, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
    | succ fuel =>
      simp only [writeLoc, EvalM.get, bind, found, writeValuePath, pure]
      exact bindRoot_events root value state

theorem execStmt_scalarExpression_events (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (expression : Expr) (origin : Goose.Core.OriginId) (form : AcceptedBinaryExpression expression) :
    KeepsConstructionEvents (execStmt fuel config environment (.expr expression origin)) := by
  cases fuel with
  | zero => simpa only [execStmt, timeout] using (KeepsConstructionEvents.stop (α := Flow) .timeout)
  | succ fuel =>
    simp only [execStmt]
    apply KeepsConstructionEvents.bind
    · exact KeepsConstructionEvents.query _ (evalValue_scalar_query form fuel config environment)
    · intro value; exact KeepsConstructionEvents.pure _

theorem execStmt_scalarLocal_events (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (id : Nat) (expression : Expr) (origin : Goose.Core.OriginId) (form : AcceptedBinaryExpression expression)
    (fixed : ∀ descriptor, environment.vars[id]? = some descriptor → descriptor.ty.nonfixed = false) :
    KeepsConstructionEvents (execStmt fuel config environment (.letS id expression origin)) := by
  cases fuel with
  | zero => simpa only [execStmt, timeout] using (KeepsConstructionEvents.stop (α := Flow) .timeout)
  | succ fuel =>
    simp only [execStmt]
    cases declared : environment.vars[id]? with
    | none => simpa only [declared, fault] using (KeepsConstructionEvents.stop (α := Flow) (.fault .unbound))
    | some descriptor =>
      simp only [declared, fixed descriptor declared, Bool.false_eq_true, ↓reduceIte]
      apply KeepsConstructionEvents.bind
      · exact KeepsConstructionEvents.query _ (stateQuery_rootOf environment id)
      · intro root
        apply KeepsConstructionEvents.bind
        · exact KeepsConstructionEvents.query _ (evalValue_scalar_query form fuel config environment)
        · intro value
          apply KeepsConstructionEvents.bind
          · exact bindRoot_events root value
          · intro result; exact KeepsConstructionEvents.pure _

theorem execStmt_scalarAssign_events (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (place : Place) (expression : Expr) (origin : Goose.Core.OriginId) (form : AcceptedBinaryExpression expression)
    (direct : (∃ id, place = .var id) ∨ ∃ id, place = .global id) :
    KeepsConstructionEvents (execStmt fuel config environment (.assign place expression origin)) := by
  cases fuel with
  | zero => simpa only [execStmt, timeout] using (KeepsConstructionEvents.stop (α := Flow) .timeout)
  | succ fuel =>
    rcases direct with ⟨id, rfl⟩ | ⟨id, rfl⟩
    · cases fuel with
      | zero =>
        intro state
        simp [execStmt, evalPlace, timeout, EvalM.stop, bind, Goose.Proofs.Exit.stepState]
      | succ fuel =>
        simp only [execStmt, evalPlace, eval_bind_assoc, eval_pure_bind]
        apply KeepsConstructionEvents.bind
        · exact KeepsConstructionEvents.query _ (stateQuery_rootOf environment id)
        · intro root
          apply KeepsConstructionEvents.bind
          · exact KeepsConstructionEvents.query _ (evalValue_scalar_query form (fuel + 1) config environment)
          · intro value
            apply KeepsConstructionEvents.bind
            · exact writeLoc_direct_events (fuel + 1) config.layout root value
            · intro result; exact KeepsConstructionEvents.pure _
    · cases fuel with
      | zero =>
        intro state
        simp [execStmt, evalPlace, timeout, EvalM.stop, bind, Goose.Proofs.Exit.stepState]
      | succ fuel =>
        simp only [execStmt, evalPlace, bind, pure]
        apply KeepsConstructionEvents.bind
        · exact KeepsConstructionEvents.query _ (evalValue_scalar_query form (fuel + 1) config environment)
        · intro value
          apply KeepsConstructionEvents.bind
          · exact writeLoc_direct_events (fuel + 1) config.layout (.global id) value
          · intro result; exact KeepsConstructionEvents.pure _

#print axioms execStmt_scalarExpression_events
#print axioms execStmt_scalarLocal_events
#print axioms execStmt_scalarAssign_events

end Goose.Proofs.ConstructionAcceptedExecution
