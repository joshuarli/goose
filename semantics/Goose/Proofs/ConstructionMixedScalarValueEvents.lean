import Goose.Proofs.ConstructionAcceptedBinaryComplete
import Goose.Proofs.ConstructionExecutionProtocolQueries

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionProtocol

theorem evalValue_scalar_leaf_query {expression : Expr} (form : AcceptedScalarExpression expression) :
    ∀ fuel config environment, StateQuery (evalValue fuel config environment expression) := by
  cases form with
  | integer ty value =>
    intro fuel config environment
    cases fuel <;> simp only [evalValue]
    · exact stateQuery_stop .timeout
    · exact stateQuery_pure _
  | boolean value =>
    intro fuel config environment
    cases fuel <;> simp only [evalValue]
    · exact stateQuery_stop .timeout
    · exact stateQuery_pure _
  | globalRead id =>
    intro fuel config environment
    cases fuel with
    | zero => simpa only [evalValue, timeout] using (stateQuery_stop (α := Value) .timeout)
    | succ fuel =>
      simp only [evalValue]
      apply stateQuery_bind
      · cases fuel <;> simp only [evalPlace]
        · exact stateQuery_stop .timeout
        · exact stateQuery_pure _
      · intro location; exact stateQuery_readLoc _ _ _
  | localRead id =>
    intro fuel config environment
    cases fuel with
    | zero => simpa only [evalValue, timeout] using (stateQuery_stop (α := Value) .timeout)
    | succ fuel =>
      simp only [evalValue]
      apply stateQuery_bind
      · cases fuel with
        | zero => simpa only [evalPlace, timeout] using (stateQuery_stop (α := Goose.Core.Loc) .timeout)
        | succ fuel =>
          simp only [evalPlace]
          apply stateQuery_bind
          · exact stateQuery_rootOf _ _
          · intro root; exact stateQuery_pure _
      · intro location; exact stateQuery_readLoc _ _ _

local macro "scalar_query_step" : tactic => `(tactic|
  first
    | with_reducible exact stateQuery_pure _
    | with_reducible exact stateQuery_stop _
    | with_reducible exact stateQuery_expectInt _
    | with_reducible exact stateQuery_expectBool _
    | with_reducible exact stateQuery_sameIntType _ _
    | with_reducible exact stateQuery_comparable _ _
    | with_reducible apply stateQuery_bind
    | (split)
    | (intro)
    | rfl)

theorem evalValue_scalar_query {expression : Expr} (form : AcceptedBinaryExpression expression) :
    ∀ fuel config environment, StateQuery (evalValue fuel config environment expression) := by
  induction form with
  | numeric form =>
    induction form with
    | scalar form =>
      induction form with
      | scalar form => exact evalValue_scalar_leaf_query form
      | not form ih =>
        intro fuel config environment
        cases fuel with
        | zero => simpa only [evalValue, timeout] using (stateQuery_stop (α := Value) .timeout)
        | succ fuel =>
          simp only [evalValue]
          repeat' first | exact ih fuel config environment | scalar_query_step
    | unary operation origin form ih =>
      intro fuel config environment
      cases fuel with
      | zero => simpa only [evalValue, timeout] using (stateQuery_stop (α := Value) .timeout)
      | succ fuel =>
        simp only [evalValue]
        repeat' first | exact ih fuel config environment | scalar_query_step
    | conversion kind target origin form ih =>
      intro fuel config environment
      cases fuel with
      | zero => simpa only [evalValue, timeout] using (stateQuery_stop (α := Value) .timeout)
      | succ fuel =>
        simp only [evalValue]
        repeat' first | exact ih fuel config environment | scalar_query_step
  | binary operation origin left right leftIH rightIH | comparison operation left right leftIH rightIH =>
    intro fuel config environment
    cases fuel with
    | zero => simpa only [evalValue, timeout] using (stateQuery_stop (α := Value) .timeout)
    | succ fuel =>
      simp only [evalValue]
      repeat' first | exact leftIH fuel config environment | exact rightIH fuel config environment | scalar_query_step
  | conjunction left right leftIH rightIH | disjunction left right leftIH rightIH =>
    intro fuel config environment
    cases fuel with
    | zero => simpa only [evalValue, timeout] using (stateQuery_stop (α := Value) .timeout)
    | succ fuel =>
      simp only [evalValue]
      repeat' first | exact leftIH fuel config environment | exact rightIH fuel config environment | scalar_query_step
  | not form ih | unary _ _ form ih | conversion _ _ _ form ih =>
    intro fuel config environment
    cases fuel with
    | zero => simpa only [evalValue, timeout] using (stateQuery_stop (α := Value) .timeout)
    | succ fuel =>
      simp only [evalValue]
      repeat' first | exact ih fuel config environment | scalar_query_step


#print axioms evalValue_scalar_query

end Goose.Proofs.ConstructionAcceptedExecution
