import Goose.Proofs.ConstructionAcceptedByteStatement
import Goose.Proofs.ExitExecutionPathContext

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem storedDestination_names_source (state : ExecutionState) (id : Nat) (stored : StoredValue)
    (sampled : storedDestination id state = .ok stored state) : stored.destination = some id := by
  simp only [storedDestination, getDestination, EvalM.get, bind] at sampled
  cases found : state.construction.destinations[id]? with
  | none => simp only [found, fault, EvalM.stop] at sampled; cases sampled
  | some row =>
    simp only [found, pure] at sampled
    cases progress : progressCount row.progress with
    | none => simp only [progress, fault, EvalM.stop] at sampled; cases sampled
    | some count =>
      simp only [progress, ExecutionStep.ok.injEq] at sampled
      obtain ⟨same, _⟩ := sampled
      cases same
      rfl

theorem reached_byte_let_published_alias (rootFuel fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (localVar : Nat) (descriptor : LocalVar) (implementation : Impl)
    (bytes : List UInt8) (origin bytesOrigin : OriginId) (before after : ExecutionState) (root : RootInst)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (reached : ExitReached rootFuel config (.statement (fuel + 2) environment
      (.letS localVar (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin)) before)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (declared : environment.vars[localVar]? = some descriptor) (ty : descriptor.ty = .varr (.int .u8))
    (implementationFound : config.module.impls[environment.implementation]? = some implementation)
    (unnamed : (implementation.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some localVar)) = none)
    (resolved : rootOf environment localVar before = .ok root before)
    (compatible : RootTypeCompatible types root (.varr (.int .u8)))
    (conforms : LayoutConforms config.layout (.varr (.int .u8)))
    (fresh : before.objectOrdinals.lookup root = none)
    (freshType : ∀ act scope id, root = .local act scope id → act < before.nextAct ∧ scope < before.nextScope)
    (freshSynthetic : ∀ id, root = .global id → config.module.globals.size ≤ id → id < config.module.globals.size + before.nextScope)
    (executed : execStmt (fuel + 2) config environment (.letS localVar (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .ok (.normal .unit) after) :
    ∃ stored published,
      ExitReached rootFuel config (.statement (fuel + 2) environment (.letS localVar (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin)) before ∧
      AcceptedWorld config initialized published ambient types live regions pending ∧
      storedDestination before.construction.destinations.size published = .ok stored published ∧
      stored.destination = some before.construction.destinations.size ∧
      bindRoot root (.stored stored) published = .ok () after ∧
      after.objects.lookup root = some (.stored stored) ∧
      AcceptedWorld config initialized after ambient (registerRootType types root (.varr (.int .u8)))
        (fun other => other = root ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))) pending := by
  obtain ⟨stored, published, fits, frame, publishedWorld, valueType, sampled, bound, extended, afterWorld⟩ :=
    execStmt_byteOwner_letWorld fuel config initialized environment localVar descriptor implementation bytes origin bytesOrigin before after root
      ambient types live regions pending world declared ty implementationFound unnamed resolved compatible conforms fresh freshType freshSynthetic executed
  have alias := storedDestination_names_source published before.construction.destinations.size stored sampled
  obtain ⟨boundState, evaluated, objects⟩ := Goose.Proofs.ConstructionRootCorrespondence.bindRoot_objects root (.stored stored) published
  have same : boundState = after := (ExecutionStep.ok.inj (evaluated.symm.trans bound)).2
  subst boundState
  have lookup : after.objects.lookup root = some (.stored stored) := by simp [objects]
  exact ⟨stored, published, reached, publishedWorld, sampled, alias, bound, lookup, afterWorld⟩

#print axioms storedDestination_names_source
#print axioms reached_byte_let_published_alias

end Goose.Proofs.ConstructionAcceptedExecution
