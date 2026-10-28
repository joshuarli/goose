import Goose.Proofs.ConstructionExitDirectReturn
import Goose.Proofs.ConstructionExitByteHandler
import Goose.Proofs.ConstructionExitProtectionCleanup
import Goose.Proofs.ConstructionExitDirectRead

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Core (OriginId ContextId ImplId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionAcceptedExecution

theorem direct_nested_byte_handler (fuel : Nat) (config : EvalConfig)
    (outer inner : RuntimeActivation) (outerPre innerPre : List (Goose.Core.VarId × Value))
    (outerScope innerScope targetId id : Nat) (bytes : List UInt8) (origin : OriginId)
    (outerRest innerRest : List Stmt) (outerTail innerTail : Option Expr)
    (contextId : ContextId) (arguments : List Arg) (callChannels : List Channel)
    (outerInitial outerBound callPrepared innerEntered innerBound : ExecutionState)
    (outerImpl innerImpl calledImpl : Impl) (calledId : ImplId)
    (outerLookup : config.module.impls[outer.implementation]? = some outerImpl)
    (results : outerImpl.results.toList.map (·.ty) = [.varr (.int .u8)])
    (outerChannels : outer.channels = [.construct id])
    (outerBinding : bindAll outer.act outerInitial.nextScope outerPre { outerInitial with
      nextScope := outerInitial.nextScope + 1
      activations := outerInitial.activations.map (fun current => if current.act == outer.act then
        { current with scopes := (outerScope, outerInitial.nextScope) :: outer.scopes } else current) } = .ok () outerBound)
    (called : getImplementation config contextId outerBound = .ok (calledId, calledImpl) outerBound)
    (callSetup : channelsFor config.layout outer.act calledImpl.results.toList origin outerBound = .ok callChannels callPrepared)
    (callPrefix : CallActivationPrefix (fuel + 7) config
      { outer with scopes := (outerScope, outerInitial.nextScope) :: outer.scopes }
      contextId arguments callChannels origin callPrepared inner innerPre
      (.mk innerScope (.returnFrom targetId [.bytes (.varr (.int .u8)) bytes origin] origin :: innerRest) innerTail) innerEntered)
    (innerLookup : config.module.impls[inner.implementation]? = some innerImpl)
    (innerBinding : bindAll inner.act innerEntered.nextScope innerPre { innerEntered with
      nextScope := innerEntered.nextScope + 1
      activations := innerEntered.activations.map (fun current => if current.act == inner.act then
        { current with scopes := (innerScope, innerEntered.nextScope) :: inner.scopes } else current) } = .ok () innerBound)
    (selection : targetActivation config targetId innerBound = .ok outer innerBound)
    (distinct : outer.act ≠ inner.act)
    (receiver : OpenDestinationBacking config.layout innerBound id (.varr (.int .u8)) 0)
    (ownership : OwnershipSourceState innerBound.construction)
    (receiverUse : receiver.destination.use = .receiver)
    (packed : receiver.destination.layout = .packed)
    (adaptation : receiver.destination.adaptation = none)
    (physical : receiver.destination.capability.layout = .varr (.int .u8))
    (request : receiver.destination.capability.request = .value)
    (current : destinationCurrent innerBound.construction id = .ok id)
    (fits : bytes.length < 2 ^ 32) :
    ∃ after final : ExecutionState,
      enterActivation (fuel + 13) config outer outerPre
        (.mk outerScope (.expr (.call contextId arguments origin) origin :: outerRest) outerTail) origin outerInitial =
        .ok [.completed id] final ∧
      final.construction.stdout = after.construction.stdout ∧
      (∀ entry : RootInst × Value,
        (Goose.Proofs.Exit.runtimeScopeRoots inner innerScope innerEntered.nextScope).contains entry.1 = false →
        (Goose.Proofs.Exit.runtimeScopeRoots outer outerScope outerInitial.nextScope).contains entry.1 = false →
        (entry ∈ final.objects ↔ entry ∈ after.objects)) ∧
      (∃ target discarded suffix, config.module.targets[targetId]? = some target ∧
        innerBound.activations = discarded ++ outer :: suffix ∧ target.contains outer.implementation = true ∧
        ∀ earlier ∈ discarded, target.contains earlier.implementation = false) ∧
      (∀ limit, limit receiver.destination.storage ≤ receiver.destination.capability.start →
        StoragePrefixesEqual limit innerBound.construction.storage final.construction.storage) ∧
      (∀ other, other ≠ id → final.construction.destinations[other]? = innerBound.construction.destinations[other]?) ∧
      (∀ root, (Goose.Proofs.Exit.runtimeScopeRoots inner innerScope innerEntered.nextScope).contains root = false →
        (Goose.Proofs.Exit.runtimeScopeRoots outer outerScope outerInitial.nextScope).contains root = false →
        final.objects.lookup root = innerBound.objects.lookup root ∧
        final.objectOrdinals.lookup root = innerBound.objectOrdinals.lookup root) ∧
      ∀ (retained : RootInst → Prop) (limit : Nat → Nat),
        validate config.module = .ok () → RootedBackingObservations config.layout innerBound retained limit →
        limit receiver.destination.storage ≤ receiver.destination.capability.start →
        (∀ root, retained root →
          (Goose.Proofs.Exit.runtimeScopeRoots inner innerScope innerEntered.nextScope).contains root = false ∧
          (Goose.Proofs.Exit.runtimeScopeRoots outer outerScope outerInitial.nextScope).contains root = false) →
        (∀ root, retained root → ∀ value, innerBound.objects.lookup root = some value →
          ∀ stored, StoredOccurrence value stored → stored.destination ≠ some id) →
        ∀ location, retained location.root → ∀ readFuel,
          mapStepState (fun _ => ExecutionState.initial) (readLoc readFuel config.layout location final) =
          mapStepState (fun _ => ExecutionState.initial) (readLoc readFuel config.layout location innerBound) := by
  let innerEnv := { inner with scopes := (innerScope, innerEntered.nextScope) :: inner.scopes }
  let outerEnv := { outer with scopes := (outerScope, outerInitial.nextScope) :: outer.scopes }
  obtain ⟨after, returned, _, _, landed, prefixes, objectFrame, ordinalFrame, rows⟩ := direct_byte_return_cleanup fuel config innerEnv outer targetId id bytes origin
    innerBound receiver ownership selection outerChannels receiverUse packed adaptation physical request current fits
  let token := innerBound.construction.exitReservations.size
  let cleaned := { after with construction := { after.construction with
    exitReservations := after.construction.exitReservations.set! token .released } }
  let innerUnwound := releaseScopeState inner innerScope innerEntered.nextScope cleaned
  let crossed := { innerUnwound with activations := innerUnwound.activations.filter (fun current => current.act != inner.act) }
  let outerUnwound := releaseScopeState outer outerScope outerInitial.nextScope crossed
  have statements : execStmts (fuel + 5) config innerEnv
      (.returnFrom targetId [.bytes (.varr (.int .u8)) bytes origin] origin :: innerRest) innerBound =
      .escape ⟨outer.act, .nonlocal targetId⟩ [.completed id] cleaned := by
    simp only [execStmts, bind, returned]
    rfl
  have innerBody : execActivationBody (fuel + 6) config inner innerPre
      (.mk innerScope (.returnFrom targetId [.bytes (.varr (.int .u8)) bytes origin] origin :: innerRest) innerTail) innerEntered =
      .escape ⟨outer.act, .nonlocal targetId⟩ [.completed id] innerUnwound := by
    unfold execActivationBody execResultScope
    have fresh : freshScope = fun state => .ok state.nextScope { state with nextScope := state.nextScope + 1 } := by
      funext state
      rfl
    rw [fresh]
    simp only [bind, EvalM.get, EvalM.set, withScope, innerBinding]
    dsimp only [innerEnv] at statements ⊢
    simp only [statements, releaseScope, bind, EvalM.get, EvalM.set]
    rfl
  have innerEscape : enterActivation (fuel + 7) config inner innerPre
      (.mk innerScope (.returnFrom targetId [.bytes (.varr (.int .u8)) bytes origin] origin :: innerRest) innerTail) origin innerEntered =
      .escape ⟨outer.act, .nonlocal targetId⟩ [.completed id] crossed := by
    simp only [enterActivation, innerLookup]
    exact Goose.Proofs.Exit.runtime_activation_propagates config.layout inner (innerImpl.results.toList.map (·.ty)) origin
      _ innerEntered innerUnwound ⟨outer.act, .nonlocal targetId⟩ [.completed id] innerBody distinct
  have callEscape := callPrefix.escape_call _ _ innerEscape
  have bodyEscape : execActivationBody (fuel + 12) config outer outerPre
      (.mk outerScope (.expr (.call contextId arguments origin) origin :: outerRest) outerTail) outerInitial =
      .escape ⟨outer.act, .nonlocal targetId⟩ [.completed id] outerUnwound := by
    unfold execActivationBody execResultScope
    have fresh : freshScope = fun state => .ok state.nextScope { state with nextScope := state.nextScope + 1 } := by
      funext state
      rfl
    rw [fresh]
    simp only [bind, EvalM.get, EvalM.set, withScope, outerBinding, execStmts, execStmt, evalValue,
      called, callSetup]
    dsimp only [outerEnv, innerUnwound, crossed, cleaned] at callEscape ⊢
    simp only [callEscape, releaseScope, bind, EvalM.get, EvalM.set]
    rfl
  let final := { outerUnwound with activations := outerUnwound.activations.filter (fun current => current.act != outer.act) }
  have finalLanded : LandedResultChannels final [.construct id] [.varr (.int .u8)] [.completed id] :=
    LandedResultChannels.of_construction_eq (before := cleaned) (after := final) rfl landed
  have finished := finalLanded.finishChannels config.layout origin
  have matched : enterActivation (fuel + 13) config outer outerPre
      (.mk outerScope (.expr (.call contextId arguments origin) origin :: outerRest) outerTail) origin outerInitial =
      .ok [.completed id] final := by
    simp only [enterActivation, outerLookup, finishActivation, bodyEscape, beq_self_eq_true, ↓reduceIte, outerChannels, results]
    change finishChannels config.layout [.construct id] [.varr (.int .u8)] [.completed id] origin final = .ok () final at finished
    rw [finished]
  have rootFrame : ∀ root, (Goose.Proofs.Exit.runtimeScopeRoots inner innerScope innerEntered.nextScope).contains root = false →
      (Goose.Proofs.Exit.runtimeScopeRoots outer outerScope outerInitial.nextScope).contains root = false →
      final.objects.lookup root = innerBound.objects.lookup root ∧
      final.objectOrdinals.lookup root = innerBound.objectOrdinals.lookup root := by
    intro root innerOutside outerOutside
    constructor
    · change (releaseScopeState outer outerScope outerInitial.nextScope crossed).objects.lookup root = _
      rw [releaseScopeState_root_lookup outer outerScope outerInitial.nextScope crossed root outerOutside]
      change (releaseScopeState inner innerScope innerEntered.nextScope cleaned).objects.lookup root = _
      rw [releaseScopeState_root_lookup inner innerScope innerEntered.nextScope cleaned root innerOutside]
      exact congrArg (fun objects => objects.lookup root) objectFrame
    · change (releaseScopeState outer outerScope outerInitial.nextScope crossed).objectOrdinals.lookup root = _
      have outerOrdinal := scope_filter_lookup_any (Goose.Proofs.Exit.runtimeScopeRoots outer outerScope outerInitial.nextScope) crossed.objectOrdinals root outerOutside
      change (releaseScopeState outer outerScope outerInitial.nextScope crossed).objectOrdinals.lookup root = crossed.objectOrdinals.lookup root at outerOrdinal
      rw [outerOrdinal]
      change (releaseScopeState inner innerScope innerEntered.nextScope cleaned).objectOrdinals.lookup root = _
      have innerOrdinal := scope_filter_lookup_any (Goose.Proofs.Exit.runtimeScopeRoots inner innerScope innerEntered.nextScope) cleaned.objectOrdinals root innerOutside
      change (releaseScopeState inner innerScope innerEntered.nextScope cleaned).objectOrdinals.lookup root = cleaned.objectOrdinals.lookup root at innerOrdinal
      rw [innerOrdinal]
      exact congrArg (fun ordinals => ordinals.lookup root) ordinalFrame
  refine ⟨after, final, matched, rfl, ?_, ?_, ?_, ?_, rootFrame, ?_⟩
  · intro entry innerOutside outerOutside
    change entry ∈ (releaseScopeState outer outerScope outerInitial.nextScope crossed).objects ↔ entry ∈ after.objects
    rw [Goose.Proofs.Exit.runtime_release_scope_outside outer outerScope outerInitial.nextScope crossed entry outerOutside]
    change entry ∈ (releaseScopeState inner innerScope innerEntered.nextScope cleaned).objects ↔ entry ∈ after.objects
    rw [Goose.Proofs.Exit.runtime_release_scope_outside inner innerScope innerEntered.nextScope cleaned entry innerOutside]
  · exact (targetActivation_selects_nearest config targetId innerBound innerBound outer selection).2
  · intro limit cutoff
    exact prefixes limit cutoff
  · intro other different
    exact rows other different
  · intro retained limit accepted valid cutoff outside names location kept readFuel
    apply direct_exit_outside_read readFuel config accepted innerBound final retained limit id valid (prefixes limit cutoff)
    · intro root member
      exact (rootFrame root (outside root member).1 (outside root member).2).1
    · intro root member
      exact (rootFrame root (outside root member).1 (outside root member).2).2
    · exact rows
    · exact names
    · exact kept

#print axioms direct_nested_byte_handler

end Goose.Proofs.ExitExecution
