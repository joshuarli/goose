import Goose.Proofs.ConstructionAcceptedByteCursor
import Goose.Proofs.ConstructionRootCorrespondenceContents

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership

theorem AcceptedFrame.visibleReferences_avoid_uninitialized
    {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    {ambient : OwnershipAmbient} {live : Goose.Core.RootInst → Prop}
    {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (source : AcceptedFrame config accepted frame state types)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (id : Nat) (root : Goose.Core.RootInst)
    (uninitialized : frame.rootCursor.nextVar ≤ id ∨ id ∈ frame.source.initializing)
    (resolved : rootOf frame.interpretation.environment id state = .ok root state)
    (other : Nat) (member : other ∈ frame.typing.visible) (actual : Goose.Core.RootInst) (location : Goose.Core.Loc)
    (otherResolved : rootOf frame.interpretation.environment other state = .ok actual state)
    (found : state.objects.lookup actual = some (.ref location)) : location.root ≠ root := by
  have noType := source.uninitializedTypes id uninitialized root resolved
  obtain ⟨descriptor, declaredRoot, oldValue, declared, oldResolved, oldFound, represented⟩ := source.locals other member
  have rootSame : declaredRoot = actual := (ExecutionStep.ok.inj (oldResolved.symm.trans otherResolved)).1
  subst declaredRoot
  have valueSame : oldValue = .ref location := Option.some.inj (oldFound.symm.trans found)
  subst oldValue
  have typingDeclared : frame.typing.variables[other]? = some descriptor := by
    simpa only [source.compatible.variables] using declared
  have pointer := (world.heap actual descriptor.ty (.ref location)
    (source.localTypes other member descriptor actual typingDeclared otherResolved) found).2
  intro equal
  generalize descriptor.ty = actualTy at pointer
  cases pointer with
  | reference mutability ty target typed =>
    obtain ⟨rootTy, registered, path⟩ := typed
    rw [equal, noType] at registered
    cases registered

theorem AcceptedFrame.bindFreshStored_correspondence
    {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {before after : ExecutionState} {types : RootTypes}
    {ambient : OwnershipAmbient} {live : Goose.Core.RootInst → Prop}
    {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (source : AcceptedFrame config accepted frame before types)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (id : Nat) (root : Goose.Core.RootInst) (stored : StoredValue)
    (uninitialized : frame.rootCursor.nextVar ≤ id ∨ id ∈ frame.source.initializing)
    (resolved : rootOf frame.interpretation.environment id before = .ok root before)
    (bound : bindRoot root (.stored stored) before = .ok () after) :
    LocalRootCorrespondence frame.interpretation frame.source.ctx (id :: frame.typing.visible) after ∧
      ∀ fuel, ContentRootCorrespondence frame.interpretation frame.source.ctx
        (id :: frame.typing.visible) fuel config.layout after := by
  have rooted : LocalValueRooted frame.interpretation frame.source.ctx id (.stored stored) := by
    intro location reference
    cases reference
  obtain ⟨directAfter, directBound, direct⟩ := bindRoot_localValueCorrespondence frame.interpretation frame.source.ctx
    frame.typing.visible before id root (.stored stored) resolved rooted source.direct
  have directSame := (ExecutionStep.ok.inj (bound.symm.trans directBound)).2
  subst directAfter
  refine ⟨direct, ?_⟩
  intro fuel
  have contentsRooted : LocalValueContentsRooted frame.interpretation frame.source.ctx id (.stored stored) fuel config.layout before := by
    intro roots annotation location equal
    cases equal
  have separateValue : ∀ location, Value.stored stored = .ref location → location.root ≠ root := by
    intro location equal
    cases equal
  have separateVisible : ∀ other ∈ frame.typing.visible, ∀ actual location,
      rootOf frame.interpretation.environment other before = .ok actual before →
      before.objects.lookup actual = some (.ref location) → location.root ≠ root := by
    intro other member actual location otherResolved found
    exact source.visibleReferences_avoid_uninitialized world id root uninitialized resolved other member actual location otherResolved found
  obtain ⟨contentAfter, contentBound, contents⟩ := bindRoot_localContentsCorrespondence frame.interpretation frame.source.ctx
    frame.typing.visible before fuel config.layout id root (.stored stored) resolved contentsRooted separateValue separateVisible
    (source.contents fuel)
  have contentSame := (ExecutionStep.ok.inj (bound.symm.trans contentBound)).2
  subst contentAfter
  exact contents

#print axioms AcceptedFrame.visibleReferences_avoid_uninitialized
#print axioms AcceptedFrame.bindFreshStored_correspondence

end Goose.Proofs.ConstructionAcceptedExecution
