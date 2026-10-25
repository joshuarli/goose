import Goose.Proofs.OwnershipAmbientContinuations

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct
open Goose.Core (ActId ImplId NonlocalTarget ScopeInst)

structure OwnershipActivationChannels where
  implementation : ImplId
  act : ActId
  channels : List Construct.Channel

def ownershipActivationChannels (activation : RuntimeActivation) : OwnershipActivationChannels :=
  ⟨activation.implementation, activation.act, activation.channels⟩

def OwnershipAmbientFrame.activationChannels : OwnershipAmbientFrame → Option OwnershipActivationChannels
  | .callChannels activation _ => some (ownershipActivationChannels activation)
  | _ => none

def OwnershipAmbientFrame.breakChannels : OwnershipAmbientFrame → Option BreakTarget
  | .breakTarget target _ => some target
  | _ => none

def OwnershipAmbient.activations (ambient : OwnershipAmbient) : List OwnershipActivationChannels :=
  ambient.filterMap OwnershipAmbientFrame.activationChannels

def OwnershipAmbient.breaks (ambient : OwnershipAmbient) : List BreakTarget :=
  ambient.filterMap OwnershipAmbientFrame.breakChannels

structure OwnershipRuntimeFrames (state : ExecutionState) (ambient : OwnershipAmbient) : Prop where
  activations : state.activations.map ownershipActivationChannels = OwnershipAmbient.activations ambient
  breaks : state.breaks = OwnershipAmbient.breaks ambient

theorem initial_ownershipRuntimeFrames : OwnershipRuntimeFrames .initial [] := ⟨rfl, rfl⟩

theorem ownershipFrame_channels_withCarriers (frame : OwnershipAmbientFrame) (carriers : List Construct.Carrier) :
    (frame.withCarriers carriers).activationChannels = frame.activationChannels ∧
      (frame.withCarriers carriers).breakChannels = frame.breakChannels := by
  cases frame <;> exact ⟨rfl, rfl⟩

theorem ownershipRuntimeFrames_returned (state : ExecutionState) (ambient : OwnershipAmbient)
    (carriers : List Construct.Carrier) :
    OwnershipRuntimeFrames state (.returned carriers :: ambient) ↔ OwnershipRuntimeFrames state ambient := by
  constructor <;> intro valid
  · exact ⟨by simpa [List.filterMap_cons, OwnershipAmbient.activations, OwnershipAmbientFrame.activationChannels] using valid.activations,
      by simpa [List.filterMap_cons, OwnershipAmbient.breaks, OwnershipAmbientFrame.breakChannels] using valid.breaks⟩
  · exact ⟨by simpa [List.filterMap_cons, OwnershipAmbient.activations, OwnershipAmbientFrame.activationChannels] using valid.activations,
      by simpa [List.filterMap_cons, OwnershipAmbient.breaks, OwnershipAmbientFrame.breakChannels] using valid.breaks⟩

theorem ownershipRuntimeFrames_capture_returned (state : ExecutionState) (frame : OwnershipAmbientFrame)
    (outer : OwnershipAmbient) (carriers : List Construct.Carrier) :
    OwnershipRuntimeFrames state (.returned carriers :: frame.withCarriers [] :: outer) ↔
      OwnershipRuntimeFrames state (frame.withCarriers carriers :: outer) := by
  cases frame <;> constructor <;> intro valid <;>
    exact ⟨by simpa [List.filterMap_cons, OwnershipAmbient.activations, OwnershipAmbientFrame.withCarriers,
        OwnershipAmbientFrame.activationChannels] using valid.activations,
      by simpa [List.filterMap_cons, OwnershipAmbient.breaks, OwnershipAmbientFrame.withCarriers,
        OwnershipAmbientFrame.breakChannels] using valid.breaks⟩

theorem ownershipRuntimeFrames_call_push (state : ExecutionState) (ambient : OwnershipAmbient)
    (activation : RuntimeActivation) (valid : OwnershipRuntimeFrames state ambient) :
    OwnershipRuntimeFrames { state with activations := activation :: state.activations }
      (.callChannels activation [] :: ambient) := by
  exact ⟨congrArg (ownershipActivationChannels activation :: ·) valid.activations, valid.breaks⟩

theorem ownershipRuntimeFrames_break_push (state : ExecutionState) (ambient : OwnershipAmbient)
    (act : ActId) (scope : BreakScope) (channels : List Construct.Channel)
    (valid : OwnershipRuntimeFrames state ambient) :
    let target : BreakTarget := ⟨state.nextScope, act, scope, channels⟩
    OwnershipRuntimeFrames { state with nextScope := state.nextScope + 1, breaks := target :: state.breaks }
      (.breakTarget target [] :: ambient) := by
  exact ⟨valid.activations, congrArg (_ :: ·) valid.breaks⟩

theorem ownershipRuntimeFrames_lookup_activation (state : ExecutionState) (ambient : OwnershipAmbient)
    (valid : OwnershipRuntimeFrames state ambient) (activation : RuntimeActivation)
    (present : activation ∈ state.activations) :
    ∃ captured carriers, OwnershipAmbientFrame.callChannels captured carriers ∈ ambient ∧
      ownershipActivationChannels captured = ownershipActivationChannels activation := by
  have member : ownershipActivationChannels activation ∈ OwnershipAmbient.activations ambient := by
    rw [← valid.activations]
    exact List.mem_map.mpr ⟨activation, present, rfl⟩
  obtain ⟨frame, framePresent, capture⟩ := List.mem_filterMap.mp member
  cases frame with
  | callChannels captured carriers =>
      exact ⟨captured, carriers, framePresent, Option.some.inj capture⟩
  | _ => simp [OwnershipAmbientFrame.activationChannels] at capture

theorem ownershipRuntimeFrames_lookup_break (state : ExecutionState) (ambient : OwnershipAmbient)
    (valid : OwnershipRuntimeFrames state ambient) (target : BreakTarget) (present : target ∈ state.breaks) :
    ∃ carriers, OwnershipAmbientFrame.breakTarget target carriers ∈ ambient := by
  rw [valid.breaks] at present
  obtain ⟨frame, framePresent, capture⟩ := List.mem_filterMap.mp present
  cases frame with
  | breakTarget captured carriers =>
      have same : captured = target := Option.some.inj capture
      subst captured
      exact ⟨carriers, framePresent⟩
  | _ => simp [OwnershipAmbientFrame.breakChannels] at capture

theorem ownershipRuntimeFrames_releaseScope (environment : RuntimeActivation) (scope : Nat) (scopeInst : ScopeInst)
    (state : ExecutionState) (ambient : OwnershipAmbient) (valid : OwnershipRuntimeFrames state ambient) :
    OwnershipRuntimeFrames (releaseScopeState environment scope scopeInst state) ambient := by
  refine ⟨?_, valid.breaks⟩
  rw [← valid.activations]
  simp only [releaseScopeState, List.map_map]
  congr 1
  funext current
  dsimp only [Function.comp_apply]
  split <;> rfl

theorem ownershipRuntimeFrames_resultScope (environment : RuntimeActivation) (scope : Nat)
    (state : ExecutionState) (ambient : OwnershipAmbient) (valid : OwnershipRuntimeFrames state ambient) :
    OwnershipRuntimeFrames (ownershipResultScopeState environment scope state) ambient := by
  refine ⟨?_, valid.breaks⟩
  rw [← valid.activations]
  simp only [ownershipResultScopeState, List.map_map]
  congr 1
  funext current
  dsimp only [Function.comp_apply]
  split <;> rfl

def OwnershipRuntimeFrameOutcome (ambient : OwnershipAmbient) : ExecutionStep α → Prop
  | .ok _ state | .escape _ _ state | .jump _ _ state => OwnershipRuntimeFrames state ambient
  | .stop _ _ => True

theorem ownershipRuntimeFrameOutcome_returned (ambient : OwnershipAmbient)
    (carriers : List Construct.Carrier) (result : ExecutionStep α) :
    OwnershipRuntimeFrameOutcome (.returned carriers :: ambient) result ↔ OwnershipRuntimeFrameOutcome ambient result := by
  cases result with
  | ok value state | escape address values state | jump target kind state =>
      exact ownershipRuntimeFrames_returned state ambient carriers
  | stop reason state => rfl

def OwnershipAmbient.withoutActivation (act : ActId) (ambient : OwnershipAmbient) : OwnershipAmbient :=
  ambient.filter fun frame => match frame with
    | .callChannels activation _ => activation.act != act
    | _ => true

def OwnershipAmbient.withoutBreak (id : Nat) (ambient : OwnershipAmbient) : OwnershipAmbient :=
  ambient.filter fun frame => match frame with
    | .breakTarget target _ => target.id != id
    | _ => true

theorem ownershipAmbient_withoutActivation_projections (act : ActId) (ambient : OwnershipAmbient) :
    OwnershipAmbient.activations (OwnershipAmbient.withoutActivation act ambient) =
      (OwnershipAmbient.activations ambient).filter (fun activation => activation.act != act) ∧
    OwnershipAmbient.breaks (OwnershipAmbient.withoutActivation act ambient) = OwnershipAmbient.breaks ambient := by
  induction ambient with
  | nil => exact ⟨rfl, rfl⟩
  | cons frame outer previous =>
      cases frame <;>
        simp only [OwnershipAmbient.withoutActivation, OwnershipAmbient.activations, OwnershipAmbient.breaks,
          List.filter_cons, List.filterMap_cons, OwnershipAmbientFrame.activationChannels,
          OwnershipAmbientFrame.breakChannels, ownershipActivationChannels] at previous ⊢
      all_goals split <;> simp_all [List.filterMap_cons, OwnershipAmbientFrame.activationChannels,
        OwnershipAmbientFrame.breakChannels, ownershipActivationChannels]

theorem ownershipAmbient_withoutBreak_projections (id : Nat) (ambient : OwnershipAmbient) :
    OwnershipAmbient.activations (OwnershipAmbient.withoutBreak id ambient) = OwnershipAmbient.activations ambient ∧
    OwnershipAmbient.breaks (OwnershipAmbient.withoutBreak id ambient) =
      (OwnershipAmbient.breaks ambient).filter (fun target => target.id != id) := by
  induction ambient with
  | nil => exact ⟨rfl, rfl⟩
  | cons frame outer previous =>
      cases frame <;>
        simp only [OwnershipAmbient.withoutBreak, OwnershipAmbient.activations, OwnershipAmbient.breaks,
          List.filter_cons, List.filterMap_cons, OwnershipAmbientFrame.activationChannels,
          OwnershipAmbientFrame.breakChannels] at previous ⊢
      all_goals split <;> simp_all [List.filterMap_cons, OwnershipAmbientFrame.activationChannels,
        OwnershipAmbientFrame.breakChannels, ownershipActivationChannels]

theorem ownershipRuntimeFrames_filter_activation (state : ExecutionState) (ambient : OwnershipAmbient)
    (act : ActId) (valid : OwnershipRuntimeFrames state ambient) :
    OwnershipRuntimeFrames { state with activations := state.activations.filter (fun current => current.act != act) }
      (OwnershipAmbient.withoutActivation act ambient) := by
  obtain ⟨activations, breaks⟩ := ownershipAmbient_withoutActivation_projections act ambient
  refine ⟨?_, valid.breaks.trans breaks.symm⟩
  rw [activations, ← valid.activations]
  simpa only [Function.comp_def, ownershipActivationChannels] using
    (List.filter_map (f := ownershipActivationChannels)
      (p := fun activation => activation.act != act) (l := state.activations)).symm

theorem ownershipRuntimeFrames_filter_break (state : ExecutionState) (ambient : OwnershipAmbient)
    (id : Nat) (valid : OwnershipRuntimeFrames state ambient) :
    OwnershipRuntimeFrames { state with breaks := state.breaks.filter (fun target => target.id != id) }
      (OwnershipAmbient.withoutBreak id ambient) := by
  obtain ⟨activations, breaks⟩ := ownershipAmbient_withoutBreak_projections id ambient
  refine ⟨valid.activations.trans activations.symm, ?_⟩
  rw [breaks, ← valid.breaks]

theorem ownershipRuntimeFrames_selectTarget (state : ExecutionState) (ambient : OwnershipAmbient)
    (valid : OwnershipRuntimeFrames state ambient) (target : NonlocalTarget) (activation : RuntimeActivation)
    (selected : selectTarget? target state.activations = some activation) :
    ∃ captured carriers, OwnershipAmbientFrame.callChannels captured carriers ∈ ambient ∧
      ownershipActivationChannels captured = ownershipActivationChannels activation := by
  apply ownershipRuntimeFrames_lookup_activation state ambient valid activation
  exact List.mem_of_find?_eq_some selected

theorem ownershipRuntimeFrames_findBreak (state : ExecutionState) (ambient : OwnershipAmbient)
    (valid : OwnershipRuntimeFrames state ambient) (act : ActId) (scope : Option BreakScope)
    (target : BreakTarget)
    (selected : state.breaks.find? (fun target => target.act == act &&
      (scope.isNone || scope == some target.scope)) = some target) :
    ∃ carriers, OwnershipAmbientFrame.breakTarget target carriers ∈ ambient := by
  exact ownershipRuntimeFrames_lookup_break state ambient valid target (List.mem_of_find?_eq_some selected)

#print axioms ownershipRuntimeFrames_filter_activation
#print axioms ownershipRuntimeFrames_filter_break
#print axioms ownershipRuntimeFrames_selectTarget
#print axioms ownershipRuntimeFrames_findBreak
#print axioms ownershipRuntimeFrames_lookup_activation
#print axioms ownershipRuntimeFrames_lookup_break
#print axioms ownershipRuntimeFrames_releaseScope
#print axioms ownershipRuntimeFrames_resultScope

end Goose.Proofs.ConstructionExecutionOwnership
