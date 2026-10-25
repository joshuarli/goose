import Goose.Proofs.ConstructionRepresentation

set_option Elab.async false

namespace Goose.Proofs.ConstructionRepresentation
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

private def ownerType : Ty := .grow (.int .i64)
private def ownerDescriptor : LocalVar := ⟨"owner", ownerType, .immutable, 0, 0⟩
private def missingOwner : StoredValue := { storage := 0, start := 0, ty := ownerType, count := 1 }
private def ownerEnvironment : RuntimeActivation := ⟨0, 0, #[ownerDescriptor], [(0, 0)], []⟩
private def ownerTyping (module : Module) : TypingEnv :=
  ⟨module, none, #[ownerDescriptor], [0], 0, 0, .ordinary, .value, [], none, 0⟩
private def missingOwnerState : ExecutionState :=
  { ExecutionState.initial with objects := [(.local 0 0 0, .stored missingOwner)] }

theorem ownershipExecutionContext_objects (state : ExecutionState) (ambient : OwnershipAmbient)
    (objects : List (Goose.Core.RootInst × Value)) (valid : OwnershipExecutionContext state ambient) :
    OwnershipExecutionContext { state with objects := objects } ambient :=
  ⟨valid.source, valid.retention, ⟨valid.runtime.activations, valid.runtime.breaks⟩,
    valid.reservations, valid.receiving, valid.bounds, ⟨valid.identities.activations, valid.identities.breaks⟩⟩

private theorem acceptedRepresentationInput_missingBacking (config : EvalConfig)
    (accepted : validate config.module = .ok ()) :
    AcceptedRepresentationInput config (ownerTyping config.module) ownerEnvironment 0 missingOwnerState [] := by
  refine ⟨⟨accepted, ?_, ?_⟩, rfl, rfl, Nat.le_refl _, ?_⟩
  · exact ownershipExecutionContext_objects .initial [] _ initial_ownershipExecutionContext
  · exact ⟨Nat.zero_le _, fun global bound => (Nat.not_lt_zero global bound).elim⟩
  · intro id visible
    have same : id = 0 := by simpa only [ownerTyping, List.mem_singleton] using visible
    subst id
    refine ⟨ownerDescriptor, .local 0 0 0, .stored missingOwner, rfl, ?_, rfl, ?_⟩
    · simp [rootOf, ownerEnvironment, ownerDescriptor, pure]
    · exact .stored ownerType missingOwner (by decide) rfl

private theorem typed_view_sample_missingBacking (fuel : Nat) (config : EvalConfig)
    (accepted : validate config.module = .ok ()) :
    AcceptedRepresentationInput config (ownerTyping config.module) ownerEnvironment 0 missingOwnerState [] ∧
    typeExpr (fuel + 3) (ownerTyping config.module) (.len (.of (.var 0))) 0 =
      .ok ([.int .i64], 0) ∧
    evalValue (fuel + 4) config ownerEnvironment (.len (.of (.var 0))) missingOwnerState =
      .stop (.fault .danglingRoot) missingOwnerState ∧
    ValueRepresentation ownerType (.stored missingOwner) ∧
    missingOwnerState.construction.storage[missingOwner.storage]? = none := by
  refine ⟨acceptedRepresentationInput_missingBacking config accepted, rfl, ?_,
    .stored ownerType missingOwner (by decide) rfl, rfl⟩
  simp [evalValue, evalView, evalPlace, rootOf, ownerEnvironment, ownerDescriptor, missingOwnerState,
    missingOwner, ExecutionState.initial, readLoc, readValuePath, arrayLength, sampledStored,
    getStorage, ConstructionState.initial, Goose.Construct.fault, EvalM.stop, EvalM.get, pure, bind]

theorem acceptedInput_typedLength_canFault (fuel : Nat) (config : EvalConfig)
    (accepted : validate config.module = .ok ()) :
    ∃ typing environment state,
      AcceptedRepresentationInput config typing environment 0 state [] ∧
      typeExpr (fuel + 3) typing (.len (.of (.var 0))) 0 = .ok ([.int .i64], 0) ∧
      evalValue (fuel + 4) config environment (.len (.of (.var 0))) state =
        .stop (.fault .danglingRoot) state := by
  have witness := typed_view_sample_missingBacking fuel config accepted
  exact ⟨ownerTyping config.module, ownerEnvironment, missingOwnerState,
    witness.1, witness.2.1, witness.2.2.1⟩

end Goose.Proofs.ConstructionRepresentation
