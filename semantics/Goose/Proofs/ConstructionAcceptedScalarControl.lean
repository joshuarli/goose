import Goose.Proofs.ConstructionAcceptedScalarGlobalRun
import Goose.Proofs.ConstructionDeliveryFlowSoundnessNoJumps
import Goose.Proofs.ExitExecutionInvocationProducersEscapeSupport

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionDelivery
open Goose.Proofs.ExitExecution

def ScalarControlFree (action : EvalM α) : Prop :=
  ProducerNeverEscapes action ∧ NeverJumps action

theorem ScalarControlFree.bind (action : EvalM α) (next : α → EvalM β)
    (first : ScalarControlFree action) (remaining : ∀ value, ScalarControlFree (next value)) :
    ScalarControlFree (action >>= next) :=
  ⟨producerNeverEscapes_bind action next first.1 (fun value => (remaining value).1),
    neverJumps_bind action next first.2 (fun value => (remaining value).2)⟩

theorem ScalarControlFree.pure (value : α) : ScalarControlFree (pure value) :=
  ⟨producerNeverEscapes_pure value, neverJumps_pure value⟩

theorem ScalarControlFree.timeout : ScalarControlFree (timeout (α := α)) :=
  ⟨producerNeverEscapes_timeout, neverJumps_stop _⟩

theorem ScalarControlFree.readLoc (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc) :
    ScalarControlFree (readLoc fuel layout location) :=
  ⟨producerNeverEscapes_readLoc fuel layout location, neverJumps_readLoc fuel layout location⟩

theorem ScalarControlFree.rootOf (environment : RuntimeActivation) (id : Nat) :
    ScalarControlFree (rootOf environment id) :=
  ⟨producerNeverEscapes_rootOf environment id, neverJumps_rootOf environment id⟩

theorem ScalarControlFree.stop (reason : Goose.Core.Stop) : ScalarControlFree (EvalM.stop (α := α) reason) := by
  constructor <;> intro <;> intro <;> intro <;> intro <;> intro impossible <;> cases impossible

theorem ScalarControlFree.expectInt (value : Value) : ScalarControlFree (expectInt value) := by
  cases value <;> first | exact ScalarControlFree.pure _ | exact ScalarControlFree.stop _

theorem ScalarControlFree.expectBool (value : Value) : ScalarControlFree (expectBool value) := by
  cases value <;> first | exact ScalarControlFree.pure _ | exact ScalarControlFree.stop _

theorem ScalarControlFree.sameIntType (first second : Goose.Core.IntTy) :
    ScalarControlFree (Goose.Construct.sameIntType first second) := by
  unfold Goose.Construct.sameIntType
  split <;> first | exact ScalarControlFree.pure _ | exact ScalarControlFree.stop _

theorem ScalarControlFree.comparable (first second : Value) : ScalarControlFree (Goose.Construct.comparable first second) := by
  cases first <;> cases second <;> simp only [Goose.Construct.comparable]
  all_goals first
    | exact ScalarControlFree.pure _
    | exact ScalarControlFree.stop _
    | (apply ScalarControlFree.bind <;> first | exact ScalarControlFree.sameIntType _ _ | (intro; exact ScalarControlFree.pure _))

theorem evalValue_scalar_leaf_controlFree {expression : Expr} (form : AcceptedScalarExpression expression) :
    ∀ fuel config environment, ScalarControlFree (evalValue fuel config environment expression) := by
  cases form with
  | integer ty value =>
    intro fuel config environment
    cases fuel <;> simp only [evalValue]
    · exact ScalarControlFree.timeout
    · exact ScalarControlFree.pure _
  | boolean value =>
    intro fuel config environment
    cases fuel <;> simp only [evalValue]
    · exact ScalarControlFree.timeout
    · exact ScalarControlFree.pure _
  | globalRead id =>
    intro fuel config environment
    cases fuel with
    | zero => simpa only [evalValue] using (ScalarControlFree.timeout (α := Value))
    | succ fuel =>
      simp only [evalValue]
      apply ScalarControlFree.bind
      · cases fuel <;> simp only [evalPlace]
        · exact ScalarControlFree.timeout
        · exact ScalarControlFree.pure _
      · intro location; exact ScalarControlFree.readLoc _ _ _
  | localRead id =>
    intro fuel config environment
    cases fuel with
    | zero => simpa only [evalValue] using (ScalarControlFree.timeout (α := Value))
    | succ fuel =>
      simp only [evalValue]
      apply ScalarControlFree.bind
      · cases fuel with
        | zero => simpa only [evalPlace] using (ScalarControlFree.timeout (α := Goose.Core.Loc))
        | succ fuel =>
          simp only [evalPlace]
          apply ScalarControlFree.bind
          · exact ScalarControlFree.rootOf _ _
          · intro root; exact ScalarControlFree.pure _
      · intro location; exact ScalarControlFree.readLoc _ _ _

local macro "scalar_control_step" : tactic => `(tactic|
  first
    | exact ScalarControlFree.pure _
    | exact ScalarControlFree.stop _
    | exact ScalarControlFree.expectInt _
    | exact ScalarControlFree.expectBool _
    | exact ScalarControlFree.sameIntType _ _
    | exact ScalarControlFree.comparable _ _
    | with_reducible apply ScalarControlFree.bind
    | (intro)
    | (split))

theorem evalValue_scalar_controlFree {expression : Expr} (form : AcceptedBinaryExpression expression) :
    ∀ fuel config environment, ScalarControlFree (evalValue fuel config environment expression) := by
  induction form with
  | numeric form =>
    induction form with
    | scalar form =>
      induction form with
      | scalar form => exact evalValue_scalar_leaf_controlFree form
      | not form ih =>
        intro fuel config environment
        cases fuel with
        | zero => simpa only [evalValue] using (ScalarControlFree.timeout (α := Value))
        | succ fuel =>
          simp only [evalValue]
          repeat' first | exact ih fuel config environment | scalar_control_step
    | unary operation origin form ih =>
      intro fuel config environment
      cases fuel with
      | zero => simpa only [evalValue] using (ScalarControlFree.timeout (α := Value))
      | succ fuel =>
        simp only [evalValue]
        repeat' first | exact ih fuel config environment | scalar_control_step
    | conversion kind target origin form ih =>
      intro fuel config environment
      cases fuel with
      | zero => simpa only [evalValue] using (ScalarControlFree.timeout (α := Value))
      | succ fuel =>
        simp only [evalValue]
        repeat' first | exact ih fuel config environment | scalar_control_step
  | binary operation origin left right leftIH rightIH | comparison operation left right leftIH rightIH =>
    intro fuel config environment
    cases fuel with
    | zero => simpa only [evalValue] using (ScalarControlFree.timeout (α := Value))
    | succ fuel =>
      simp only [evalValue]
      repeat' first | exact leftIH fuel config environment | exact rightIH fuel config environment | scalar_control_step
  | conjunction left right leftIH rightIH | disjunction left right leftIH rightIH =>
    intro fuel config environment
    cases fuel with
    | zero => simpa only [evalValue] using (ScalarControlFree.timeout (α := Value))
    | succ fuel =>
      simp only [evalValue]
      repeat' first | exact leftIH fuel config environment | exact rightIH fuel config environment | scalar_control_step
  | not form ih | unary _ _ form ih | conversion _ _ _ form ih =>
    intro fuel config environment
    cases fuel with
    | zero => simpa only [evalValue] using (ScalarControlFree.timeout (α := Value))
    | succ fuel =>
      simp only [evalValue]
      repeat' first | exact ih fuel config environment | scalar_control_step

theorem execStmts_scalar_controlFree {statements : List Stmt} (form : ScalarExpressionStatements statements) :
    ∀ fuel config environment, ScalarControlFree (execStmts fuel config environment statements) := by
  induction form with
  | nil =>
    intro fuel config environment
    cases fuel <;> simp only [execStmts]
    · exact ScalarControlFree.timeout
    · exact ScalarControlFree.pure _
  | cons expression origin rest head tail ih =>
    intro fuel config environment
    cases fuel with
    | zero => simpa only [execStmts] using (ScalarControlFree.timeout (α := Flow))
    | succ fuel =>
      simp only [execStmts]
      apply ScalarControlFree.bind
      · cases fuel with
        | zero => simpa only [execStmt] using (ScalarControlFree.timeout (α := Flow))
        | succ fuel =>
          simp only [execStmt]
          apply ScalarControlFree.bind
          · exact evalValue_scalar_controlFree head fuel config environment
          · intro; exact ScalarControlFree.pure _
      · intro flow
        cases flow with
        | normal value => exact ih fuel config environment
        | breaking target => exact ScalarControlFree.pure _
        | continuing => exact ScalarControlFree.pure _

#print axioms execStmts_scalar_controlFree
#print axioms evalValue_scalar_controlFree
#print axioms evalValue_scalar_leaf_controlFree
end Goose.Proofs.ConstructionAcceptedExecution
