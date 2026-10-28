import Goose.Proofs.ConstructionAcceptedCursor
import Goose.Proofs.ConstructionFixedValueBacking

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

private theorem localRead_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

theorem typeExpr_localRead_descriptor (fuel : Nat) (environment : TypingEnv) (id : Nat)
    (before after : Nat) (ty : Ty)
    (checked : typeExpr fuel environment (.read (.var id)) before = .ok ([ty], after)) :
    ∃ descriptor, id ∈ environment.visible ∧ environment.variables[id]? = some descriptor ∧
      ty = descriptor.ty ∧ after = before ∧ descriptor.ty.nonfixed = false := by
  cases fuel with
  | zero => change Except.error _ = Except.ok _ at checked; cases checked
  | succ fuel =>
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at checked; cases checked
    | succ fuel =>
      simp only [typeExpr, typePlace, bind, StateT.bind] at checked
      obtain ⟨place, placeChecked, returned⟩ := localRead_bind_success _ _ _ checked
      obtain ⟨descriptor, lookup, placeReturned⟩ := localRead_bind_success _ _ _ placeChecked
      change ((do
        if !environment.visible.contains id then throw (⟨.type, "localVar is not visible"⟩ : Goose.Core.Rejection)
        let some decl := environment.variables[id]? | throw (⟨.type, "localVar outside table"⟩ : Goose.Core.Rejection)
        pure decl) : TypingM LocalVar) before = .ok descriptor at lookup
      cases contains : environment.visible.contains id with
      | false => simp only [contains, Bool.not_false, ↓reduceIte] at lookup; change Except.error _ = Except.ok _ at lookup; cases lookup
      | true =>
        simp only [contains, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at lookup
        cases declared : environment.variables[id]? with
        | none => simp only [declared] at lookup; change Except.error _ = Except.ok _ at lookup; cases lookup
        | some decl =>
          simp only [declared] at lookup
          change Except.ok (decl, before) = Except.ok descriptor at lookup
          simp only [Except.ok.injEq] at lookup
          obtain ⟨rfl, rfl⟩ := lookup
          simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at placeReturned
          subst place
          simp only [Except.bind, pure, StateT.pure] at returned
          obtain ⟨result, required, returned⟩ := localRead_bind_success _ _ _ returned
          cases returned
          cases valid : (decl.ty.storable && !decl.ty.nonfixed) with
          | false => simp only [valid] at required; change Except.error _ = Except.ok _ at required; cases required
          | true =>
            simp only [valid] at required
            change Except.ok ((), before) = Except.ok result at required
            cases required
            have fixed : decl.ty.nonfixed = false := by
              cases nonfixed : decl.ty.nonfixed <;> simp_all
            exact ⟨decl, List.contains_iff_mem.mp contains, rfl, rfl, rfl, fixed⟩

theorem localRead_provenance_nextVar (frame : ConstructionSourceFrame) (id : Nat)
    (roots : List RootRef) (after : RState)
    (checked : rpExpr frame.source (.read (.var id)) frame.rootCursor = .ok (roots, after)) :
    after.nextVar = frame.rootCursor.nextVar := by
  cases declared : frame.source.impl.vars[id]? with
  | none =>
    have extracted := congrArg
      (fun result : Except Goose.Core.Rejection (List RootRef × RState) => result.toOption.map (fun pair => pair.2.nextVar)) checked
    simp [rpExpr, rpPlace, readRoots, declared, addReads, addRoots, modify, bind, pure] at extracted
    change some frame.rootCursor.nextVar = some after.nextVar at extracted
    exact (Option.some.inj extracted).symm
  | some descriptor =>
    cases refLike : descriptor.ty.isRefLike with
    | false =>
      have extracted := congrArg
        (fun result : Except Goose.Core.Rejection (List RootRef × RState) => result.toOption.map (fun pair => pair.2.nextVar)) checked
      simp [rpExpr, rpPlace, readRoots, declared, refLike, addReads, addRoots, modify, bind, pure] at extracted
      change some frame.rootCursor.nextVar = some after.nextVar at extracted
      exact (Option.some.inj extracted).symm
    | true =>
      cases annotated : frame.source.ann id with
      | none =>
        simp [rpExpr, rpPlace, readRoots, declared, refLike, annotated, addReads, addRoots, modify, bind, pure] at checked
        change Except.error _ = Except.ok _ at checked
        cases checked
      | some annotation =>
        have extracted := congrArg
          (fun result : Except Goose.Core.Rejection (List RootRef × RState) => result.toOption.map (fun pair => pair.2.nextVar)) checked
        simp [rpExpr, rpPlace, readRoots, declared, refLike, annotated, addReads, addRoots, modify, bind, pure] at extracted
        change some frame.rootCursor.nextVar = some after.nextVar at extracted
        exact (Option.some.inj extracted).symm

#print axioms localRead_provenance_nextVar
theorem localRead_annotated_roots (frame : ConstructionSourceFrame) (id : Nat) (descriptor : LocalVar)
    (annotation roots : List RootRef) (after : RState)
    (declared : frame.source.impl.vars[id]? = some descriptor) (refLike : descriptor.ty.isRefLike = true)
    (annotated : frame.source.ann id = some annotation)
    (checked : rpExpr frame.source (.read (.var id)) frame.rootCursor = .ok (roots, after)) : roots = annotation := by
  have extracted := congrArg
    (fun result : Except Goose.Core.Rejection (List RootRef × RState) => result.toOption.map Prod.fst) checked
  simp [rpExpr, rpPlace, readRoots, declared, refLike, annotated, addReads, addRoots, modify, bind, pure] at extracted
  change some annotation = some roots at extracted
  exact (Option.some.inj extracted).symm

#print axioms localRead_annotated_roots
theorem checkedLocalRead_typeValidated (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes)
    (source : AcceptedFrame config accepted frame state types) (id : Nat) (descriptor : LocalVar)
    (declared : frame.typing.variables[id]? = some descriptor) :
    checkType config.module descriptor.ty = .ok () ∨
      ∃ mutability target, descriptor.ty = .ref mutability target ∧ checkType config.module target = .ok () := by
  have original := source.compatible.origin
  unfold SourceOrigin at original
  cases phase : frame.phase with
  | initializer global =>
    rw [phase] at original
    obtain ⟨_, _, _, _, _, implementation, _⟩ := original
    have empty : frame.source.impl.vars[id]? = some descriptor := by
      rw [source.compatible.sourceVariables]; exact declared
    rw [implementation] at empty
    simp [initImpl] at empty
  | implementation context =>
    rw [phase] at original
    obtain ⟨entry, calls, contextFound, implementationFound, implementationId, rest⟩ := original
    have present : frame.source.impl.vars[id]? = some descriptor := by
      rw [source.compatible.sourceVariables]; exact declared
    exact validated_local_type_or_reference config.module entry.impl frame.source.impl id descriptor accepted.accepted implementationFound present

#print axioms checkedLocalRead_typeValidated
private theorem localRead_reference_refLike (ty : Ty) (value : Value) (location : Goose.Core.Loc)
    (represented : ValueRepresentation ty value) (reference : DirectReference value location) : ty.isRefLike = true := by
  cases reference <;> cases represented <;> rfl

theorem evalValue_checkedLocalRead_accepted (fuel : Nat) (config : EvalConfig)
    (accepted : AcceptedModule config) (frame : ConstructionSourceFrame) (state : ExecutionState)
    (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (id : Nat) (ty : Ty)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame (.read (.var id)) ty roots typingAfter rootsAfter) :
    ∃ value, evalValue (fuel + 2) config frame.interpretation.environment (.read (.var id)) state = .ok value state ∧
      AcceptedValue config.layout types frame.interpretation state ty roots value := by
  obtain ⟨descriptor, visible, declared, sameTy, _, fixed⟩ :=
    typeExpr_localRead_descriptor frame.typingFuel frame.typing id frame.typingCounter typingAfter ty checked.typing
  obtain ⟨runtimeDescriptor, root, value, runtimeDeclared, resolved, found, represented⟩ := source.locals id visible
  have expected : frame.interpretation.environment.vars[id]? = some descriptor := by
    rw [source.compatible.variables]; exact declared
  have sameDescriptor : runtimeDescriptor = descriptor := Option.some.inj (runtimeDeclared.symm.trans expected)
  subst runtimeDescriptor ty
  have registered := source.localTypes id visible descriptor root declared resolved
  have validated := checkedLocalRead_typeValidated config accepted frame state types source id descriptor declared
  have backed : ValueStorageBacked config.layout state value := by
    rcases validated with checkedType | ⟨mutability, target, same, checkedTarget⟩
    · exact represented.checked_fixed_storageBacked config.module config.layout state descriptor.ty value checkedType fixed
    · rw [same] at represented
      cases represented with
      | reference mutability target location => exact .reference location
      | stored ty stored nonfixed logical => cases nonfixed
  refine ⟨value, ?_, represented, (world.heap root descriptor.ty value registered found).2, backed, ?_⟩
  · simp only [evalValue, evalPlace, resolved, bind, pure, readLoc, EvalM.get, found, readValuePath]
  · intro location reference
    obtain ⟨annotation, annotated, rooted⟩ := source.direct id visible root value resolved found location reference
    have refLike := localRead_reference_refLike descriptor.ty value location represented reference
    have sourceDeclared : frame.source.impl.vars[id]? = some descriptor := by
      rw [source.compatible.sourceVariables]; exact declared
    have annotation' : frame.source.ann id = some annotation := annotated
    have same := localRead_annotated_roots frame id descriptor annotation roots rootsAfter sourceDeclared refLike annotation' checked.provenance
    rw [same]
    exact rooted

#print axioms evalValue_checkedLocalRead_accepted
#print axioms typeExpr_localRead_descriptor
end Goose.Proofs.ConstructionAcceptedExecution
