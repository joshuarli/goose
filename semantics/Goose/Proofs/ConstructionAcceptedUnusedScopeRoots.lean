import Goose.Proofs.ConstructionAcceptedUnusedScope

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem instantiates_leaveScope_withoutDeclarations (interpretation : RootInterpretation) (scope scopeInst : Nat)
    (absent : ∀ descriptor ∈ interpretation.environment.vars.toList, descriptor.scope ≠ scope)
    (symbolic : RootRef) (root : Goose.Core.RootInst)
    (actual : Instantiates (interpretation.enterScope scope scopeInst) symbolic root) :
    Instantiates interpretation symbolic root := by
  cases actual with
  | global id declared => exact .global id declared
  | static id synthetic => exact .static id synthetic
  | parameter id root supplied => exact .parameter id root supplied
  | «local» id descriptor oldInstance declared active =>
    have declared' : interpretation.environment.vars[id]? = some descriptor := declared
    have member : descriptor ∈ interpretation.environment.vars.toList :=
      Array.mem_toList_iff.mpr (Array.mem_of_getElem? declared')
    have different : (scope == descriptor.scope) = false := beq_eq_false_iff_ne.mpr (absent descriptor member).symm
    apply Instantiates.local id descriptor oldInstance declared'
    simpa [RootInterpretation.enterScope, different] using active

theorem rootIn_leaveScope_withoutDeclarations (interpretation : RootInterpretation) (scope scopeInst : Nat)
    (absent : ∀ descriptor ∈ interpretation.environment.vars.toList, descriptor.scope ≠ scope)
    (roots : List RootRef) (root : Goose.Core.RootInst)
    (actual : RootIn (interpretation.enterScope scope scopeInst) roots root) : RootIn interpretation roots root := by
  obtain ⟨symbolic, member, instantiated⟩ := actual
  exact ⟨symbolic, member, instantiates_leaveScope_withoutDeclarations interpretation scope scopeInst absent symbolic root instantiated⟩

theorem AcceptedFrame.leaveScope_withoutDeclarations {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {before after : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame before types) (scope scopeInst fuel : Nat)
    (absent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ scope)
    (child : AcceptedFrame config accepted (unusedChildScopeFrame frame scope scopeInst fuel) after types) :
    AcceptedFrame config accepted frame after types := by
  have roots := rootOf_enterScope_withoutDeclarations frame.interpretation scope scopeInst
  refine ⟨source.compatible, ?_, ?_, source.initializingBefore, source.aliases, ?_, ?_, ?_, ?_, child.futureGlobals, ?_, ?_⟩
  · simpa [RootFrontier, unusedChildScopeFrame, RootInterpretation.enterScope] using child.frontier
  · intro entry member
    apply child.scopeFrontier entry
    simp [unusedChildScopeFrame, RootInterpretation.enterScope, member]
  · intro id member
    obtain ⟨descriptor, root, value, declared, resolved, found, represented⟩ := child.locals id member
    exact ⟨descriptor, root, value, declared, by simpa [unusedChildScopeFrame, roots id absent] using resolved, found, represented⟩
  · intro id member descriptor root declared resolved
    apply child.localTypes id member descriptor root declared
    simpa [unusedChildScopeFrame, roots id absent] using resolved
  · intro id condition root resolved
    apply child.uninitializedLocals id condition root
    simpa [unusedChildScopeFrame, roots id absent] using resolved
  · intro id condition root resolved
    apply child.uninitializedTypes id condition root
    simpa [unusedChildScopeFrame, roots id absent] using resolved
  · intro id member root value resolved found location reference
    have resolved' : rootOf (unusedChildScopeFrame frame scope scopeInst fuel).interpretation.environment id after = .ok root after := by
      simpa [unusedChildScopeFrame, roots id absent] using resolved
    obtain ⟨symbolic, annotation, rooted⟩ := child.direct id member root value resolved' found location reference
    exact ⟨symbolic, annotation, rootIn_leaveScope_withoutDeclarations frame.interpretation scope scopeInst absent symbolic location.root rooted⟩
  · intro readFuel id member symbolic annotation root location value resolved found read interior reference
    have resolved' : rootOf (unusedChildScopeFrame frame scope scopeInst fuel).interpretation.environment id after = .ok root after := by
      simpa [unusedChildScopeFrame, roots id absent] using resolved
    have rooted := child.contents readFuel id member symbolic annotation root location value resolved' found read interior reference
    exact rootIn_leaveScope_withoutDeclarations frame.interpretation scope scopeInst absent symbolic interior.root rooted

#print axioms AcceptedFrame.leaveScope_withoutDeclarations
#print axioms instantiates_leaveScope_withoutDeclarations
#print axioms rootIn_leaveScope_withoutDeclarations
end Goose.Proofs.ConstructionAcceptedExecution
