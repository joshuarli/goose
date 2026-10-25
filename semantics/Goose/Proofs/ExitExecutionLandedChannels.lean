import Goose.Construct.Eval

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Core (DestinationId OriginId)

structure NormalizedCompletedCarrier (state : ExecutionState) (result : Ty) (id : DestinationId) where
  destination : PendingDestination
  present : state.construction.destinations[id]? = some destination
  built : ∃ count, destination.progress = .built count
  writable : destinationCanWrite state.construction id = true
  adaptation : destination.adaptation = none
  normalized : (destination.layout == .packed && destination.capability.request == .value &&
    !(match destination.capability.layout with | .varr _ => true | _ => false)) = false
  type : destination.capability.logicalType = result
  constructible : result.constructible = true

inductive LandedResultChannel (state : ExecutionState) : Channel → Ty → Carrier → Prop
  | register (result : Ty) (value : Value) :
      LandedResultChannel state (.register result) result (.register value)
  | construct (incoming id : DestinationId) (result : Ty)
      (receiving : destinationCurrent state.construction incoming = .ok id)
      (completed : NormalizedCompletedCarrier state result id) :
      LandedResultChannel state (.construct incoming) result (.completed id)
  | completion (token incoming selected id : Nat) (role : ExitReservationRole) (snapshot : PendingDestination) (result : Ty)
      (ticket : state.construction.exitReservations[token]? = some (.active role incoming selected snapshot))
      (receiving : destinationCurrent state.construction selected = .ok id)
      (completed : NormalizedCompletedCarrier state result id) :
      LandedResultChannel state (.completion token) result (.completed id)

inductive LandedResultChannels (state : ExecutionState) : List Channel → List Ty → List Carrier → Prop
  | nil : LandedResultChannels state [] [] []
  | cons {channel result carrier channels results carriers}
      (head : LandedResultChannel state channel result carrier)
      (tail : LandedResultChannels state channels results carriers) :
      LandedResultChannels state (channel :: channels) (result :: results) (carrier :: carriers)

private theorem adaptDestinationType_normalized (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination) (result : Ty)
    (present : state.destinations[id]? = some destination)
    (built : ∃ count, destination.progress = .built count)
    (writable : destinationCanWrite state id = true)
    (type : destination.capability.logicalType = result)
    (constructible : result.constructible = true) :
    adaptDestinationType id result state = .ok () state := by
  have compatible : result.adaptsTo result = true := by simp only [Ty.adaptsTo, beq_self_eq_true, Bool.true_or]
  obtain ⟨count, progress⟩ := built
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have unchanged : { destination with capability := { destination.capability with logicalType := result } } = destination := by
    rw [← type]
  have setSame : state.destinations.set! id destination = state.destinations := by
    rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def]
    simp only [inside, ↓reduceDIte]
    have same := (Array.getElem?_eq_some_iff.mp present).2
    rw [← same]
    exact Array.set_getElem_self inside
  simp only [adaptDestinationType, writableDestination_result, present, writable, bind, progress,
    constructible, type, compatible, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  simp only [progress] at unchanged
  rw [unchanged, replaceDestination_result]
  simp only [inside, ↓reduceIte, setSame]

theorem NormalizedCompletedCarrier.finishChannel (state : ExecutionState) (result : Ty) (id : DestinationId)
    (valid : NormalizedCompletedCarrier state result id) (layout : LayoutEnv) (origin : OriginId) :
    finishChannel layout origin (.completed id) result state = .ok () state := by
  have adapted := adaptDestinationType_normalized state.construction id valid.destination result
    valid.present valid.built valid.writable valid.type valid.constructible
  simp only [Goose.Construct.finishChannel, getDestination, EvalM.get, bind, pure, valid.present, valid.adaptation,
    Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  erw [valid.normalized]
  simp only [Bool.false_eq_true, ↓reduceIte, liftConstruction, adapted]


theorem LandedResultChannels.lengths {state : ExecutionState} {channels : List Channel}
    {results : List Ty} {carriers : List Carrier}
    (valid : LandedResultChannels state channels results carriers) :
    channels.length = carriers.length ∧ carriers.length = results.length := by
  induction valid with
  | nil => exact ⟨rfl, rfl⟩
  | cons head tail ih => simpa only [List.length_cons, Nat.succ.injEq] using ih

theorem LandedResultChannels.landCarriersInto {state : ExecutionState} {channels : List Channel}
    {results : List Ty} {carriers : List Carrier}
    (valid : LandedResultChannels state channels results carriers) (origin : OriginId) :
    Goose.Construct.landCarriersInto origin channels carriers state = .ok () state := by
  induction valid with
  | nil => simp only [Goose.Construct.landCarriersInto, List.length_nil, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, List.zip_nil_left, List.forIn_nil, bind, pure]
  | cons head tail ih =>
      obtain ⟨length, _⟩ := tail.lengths
      simp only [Goose.Construct.landCarriersInto, List.length_cons, length, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.forIn_cons, bind, pure] at ih ⊢
      cases head with
      | register result value => simpa only [bind, pure] using ih
      | construct incoming id result receiving completed =>
          simpa only [receivingDestination, liftConstruction, receiving, bind, bne_self_eq_false,
            Bool.false_eq_true, ↓reduceIte, pure] using ih
      | completion token incoming selected id role snapshot result ticket receiving completed =>
          simpa only [EvalM.get, bind, ticket, receivingDestination, liftConstruction, receiving,
            bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure] using ih


theorem LandedResultChannel.finishChannel {state : ExecutionState} {channel : Channel}
    {result : Ty} {carrier : Carrier} (valid : LandedResultChannel state channel result carrier)
    (layout : LayoutEnv) (origin : OriginId) :
    Goose.Construct.finishChannel layout origin carrier result state = .ok () state := by
  cases valid with
  | register result value => rfl
  | construct incoming id result receiving completed => exact completed.finishChannel state result id layout origin
  | completion token incoming selected id role snapshot result ticket receiving completed =>
      exact completed.finishChannel state result id layout origin

theorem LandedResultChannels.finishChannels {state : ExecutionState} {channels : List Channel}
    {results : List Ty} {carriers : List Carrier}
    (valid : LandedResultChannels state channels results carriers) (layout : LayoutEnv) (origin : OriginId) :
    Goose.Construct.finishChannels layout channels results carriers origin state = .ok () state := by
  induction valid with
  | nil => simp only [Goose.Construct.finishChannels, LandedResultChannels.nil.landCarriersInto origin,
      bind, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      List.zip_nil_left, List.forIn_nil, pure]
  | cons head tail ih =>
      have landed := (LandedResultChannels.cons head tail).landCarriersInto origin
      have tailLanded := tail.landCarriersInto origin
      have finished := head.finishChannel layout origin
      obtain ⟨_, length⟩ := tail.lengths
      simp only [Goose.Construct.finishChannels, landed, tailLanded, List.length_cons, length,
        bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons,
        List.forIn_cons, bind, pure, finished] at ih ⊢
      exact ih


def NormalizedCompletedCarrier.of_construction_eq {before after : ExecutionState}
    (same : after.construction = before.construction) {result : Ty} {id : DestinationId}
    (valid : NormalizedCompletedCarrier before result id) : NormalizedCompletedCarrier after result id where
  destination := valid.destination
  present := by rw [same]; exact valid.present
  built := valid.built
  writable := by rw [same]; exact valid.writable
  adaptation := valid.adaptation
  normalized := valid.normalized
  type := valid.type
  constructible := valid.constructible

theorem LandedResultChannel.of_construction_eq {before after : ExecutionState}
    (same : after.construction = before.construction) {channel : Channel} {result : Ty} {carrier : Carrier}
    (valid : LandedResultChannel before channel result carrier) :
    LandedResultChannel after channel result carrier := by
  cases valid with
  | register result value => exact .register result value
  | construct incoming id result receiving completed =>
      exact .construct incoming id result (by rw [same]; exact receiving)
        (completed.of_construction_eq same)
  | completion token incoming selected id role snapshot result ticket receiving completed =>
      exact .completion token incoming selected id role snapshot result
        (by rw [same]; exact ticket) (by rw [same]; exact receiving)
        (completed.of_construction_eq same)

theorem LandedResultChannels.of_construction_eq {before after : ExecutionState}
    (same : after.construction = before.construction) {channels : List Channel}
    {results : List Ty} {carriers : List Carrier}
    (valid : LandedResultChannels before channels results carriers) :
    LandedResultChannels after channels results carriers := by
  induction valid with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.of_construction_eq same) ih

theorem finishActivation_catches_landed (layout : LayoutEnv) (activation : RuntimeActivation)
    (results : List Ty) (origin : OriginId) (action : EvalM (List Carrier))
    (initial after : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (evaluated : action initial = .escape address carriers after)
    (caught : address.activation = activation.act)
    (landed : LandedResultChannels after activation.channels results carriers) :
    finishActivation layout activation results origin action initial =
      .ok carriers { after with activations := after.activations.filter (fun current => current.act != activation.act) } := by
  have completed := (landed.of_construction_eq (before := after) (after :=
    { after with activations := after.activations.filter (fun current => current.act != activation.act) }) rfl).finishChannels layout origin
  simp only [finishActivation, evaluated, caught, beq_self_eq_true, ↓reduceIte, completed]

theorem finishActivation_returns_landed (layout : LayoutEnv) (activation : RuntimeActivation)
    (results : List Ty) (origin : OriginId) (action : EvalM (List Carrier))
    (initial after : ExecutionState) (carriers : List Carrier)
    (evaluated : action initial = .ok carriers after)
    (landed : LandedResultChannels after activation.channels results carriers) :
    finishActivation layout activation results origin action initial =
      .ok carriers { after with activations := after.activations.filter (fun current => current.act != activation.act) } := by
  have completed := (landed.of_construction_eq (before := after) (after :=
    { after with activations := after.activations.filter (fun current => current.act != activation.act) }) rfl).finishChannels layout origin
  simp only [finishActivation, evaluated, completed]

#print axioms NormalizedCompletedCarrier.finishChannel
#print axioms LandedResultChannels.lengths
#print axioms LandedResultChannels.landCarriersInto
#print axioms LandedResultChannel.finishChannel
#print axioms LandedResultChannels.finishChannels
#print axioms NormalizedCompletedCarrier.of_construction_eq
#print axioms LandedResultChannel.of_construction_eq
#print axioms LandedResultChannels.of_construction_eq
#print axioms finishActivation_catches_landed
#print axioms finishActivation_returns_landed

end Goose.Proofs.ExitExecution
