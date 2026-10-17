import Goose.Construct.Runtime
import Lean.Elab.Tactic

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

def NeverJumps (action : EvalM α) : Prop :=
  ∀ state target kind after, action state ≠ .jump target kind after

theorem neverJumps_pure (value : α) : NeverJumps (pure value) := by
  intro state target kind after impossible
  cases impossible

theorem neverJumps_stop (reason : Goose.Core.Stop) :
    NeverJumps (EvalM.stop (α := α) reason) := by
  intro state target kind after impossible
  cases impossible

theorem neverJumps_get : NeverJumps EvalM.get := by
  intro state target kind after impossible
  cases impossible

theorem neverJumps_bind (action : EvalM α) (next : α → EvalM β)
    (head : NeverJumps action) (tail : ∀ value, NeverJumps (next value)) :
    NeverJumps (action >>= next) := by
  intro state target kind after impossible
  cases evaluated : action state with
  | ok value middle =>
      simp only [bind, Bind.bind, evaluated] at impossible
      exact tail value middle target kind after impossible
  | stop reason middle =>
      simp only [bind, Bind.bind, evaluated] at impossible
      cases impossible
  | escape address carriers middle =>
      simp only [bind, Bind.bind, evaluated] at impossible
      cases impossible
  | jump other jumpKind middle => exact head state other jumpKind middle evaluated

theorem neverJumps_lift (origin : Goose.Core.OriginId) (action : ConstructionM α) :
    NeverJumps (liftConstruction origin action) := by
  intro state target kind after impossible
  cases evaluated : action state.construction <;>
    simp only [liftConstruction, evaluated] at impossible <;> cases impossible

theorem neverJumps_forIn (items : List α) (initial : β)
    (action : α → β → EvalM (ForInStep β))
    (body : ∀ item value, NeverJumps (action item value)) :
    NeverJumps (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact neverJumps_pure _
  | cons item rest ih =>
      rw [List.forIn_cons]
      apply neverJumps_bind
      · exact body item initial
      · intro step
        cases step with
        | done value => exact neverJumps_pure _
        | yield value => exact ih value

theorem neverJumps_getDestination (id : Goose.Core.DestinationId) :
    NeverJumps (getDestination id) := by
  unfold getDestination
  apply neverJumps_bind
  · exact neverJumps_get
  · intro state
    split
    · exact neverJumps_pure _
    · exact neverJumps_stop _

theorem neverJumps_receivingLayout (layout : LayoutEnv) (ty : Ty) :
    NeverJumps (receivingLayout layout ty) := by
  cases ty <;> simp only [receivingLayout]
  all_goals first | exact neverJumps_pure _ | exact neverJumps_stop _ | skip
  split
  · exact neverJumps_pure _
  · exact neverJumps_stop _

theorem neverJumps_conditional (condition : Prop) [Decidable condition]
    (yes no : EvalM α) (left : NeverJumps yes) (right : NeverJumps no) :
    NeverJumps (if condition then yes else no) := by
  split <;> assumption

local elab "finish_conditional" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``NeverJumps do throwError "expected jump exclusion"
  let arguments := target.getAppArgs
  let some action := arguments[arguments.size - 1]? | throwError "expected action"
  unless action.getAppFn.isConstOf ``ite do throwError "expected conditional action"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply neverJumps_conditional))

local elab "finish_intro" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isForall do throwError "expected callback"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro))

local elab "finish_zeta" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``NeverJumps do throwError "expected jump exclusion"
  let arguments := target.getAppArgs
  let some action := arguments[arguments.size - 1]? | throwError "expected action"
  unless action.isLet do throwError "expected local action binding"
  Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only))

local macro "finish_control" : tactic => `(tactic|
  repeat' first
    | exact neverJumps_pure _
    | exact neverJumps_stop _
    | exact neverJumps_get
    | exact neverJumps_getDestination _
    | exact neverJumps_receivingLayout _ _
    | (with_reducible apply neverJumps_lift)
    | (with_reducible apply neverJumps_bind)
    | (with_reducible apply neverJumps_forIn)
    | finish_conditional
    | finish_zeta
    | finish_intro
    | split
    | unfold receivingDestination)

theorem neverJumps_finishChannel (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (carrier : Carrier) (result : Ty) : NeverJumps (finishChannel layout origin carrier result) := by
  cases carrier <;> unfold finishChannel <;> finish_control

theorem neverJumps_landCarriersInto (origin : Goose.Core.OriginId)
    (channels : List Channel) (carriers : List Carrier) :
    NeverJumps (landCarriersInto origin channels carriers) := by
  unfold landCarriersInto
  finish_control
  all_goals split <;> finish_control

theorem neverJumps_finishChannels (layout : LayoutEnv) (channels : List Channel)
    (types : List Ty) (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    NeverJumps (finishChannels layout channels types carriers origin) := by
  unfold finishChannels
  apply neverJumps_bind
  · exact neverJumps_landCarriersInto origin channels carriers
  · intro _
    finish_control
    exact neverJumps_finishChannel _ _ _ _

theorem finishActivation_no_jump (layout : LayoutEnv) (activation : RuntimeActivation)
    (types : List Ty) (origin : Goose.Core.OriginId) (action : EvalM (List Carrier))
    (state : ExecutionState) (target : Nat) (kind : JumpKind) (after : ExecutionState) :
    finishActivation layout activation types origin action state ≠ .jump target kind after := by
  cases evaluated : action state with
  | ok carriers middle =>
      simp only [finishActivation, evaluated]
      split <;> intro impossible <;> try cases impossible
      exact neverJumps_finishChannels layout activation.channels types carriers origin _ _ _ _ (by assumption)
  | stop reason middle =>
      simp only [finishActivation, evaluated]
      intro impossible; cases impossible
  | escape address carriers middle =>
      simp only [finishActivation, evaluated]
      split
      · split <;> intro impossible <;> try cases impossible
        exact neverJumps_finishChannels layout activation.channels types carriers origin _ _ _ _ (by assumption)
      · intro impossible; cases impossible
  | jump other jumpKind middle =>
      simp only [finishActivation, evaluated]
      intro impossible; cases impossible

#print axioms finishActivation_no_jump

end Goose.Proofs.ConstructionDelivery
