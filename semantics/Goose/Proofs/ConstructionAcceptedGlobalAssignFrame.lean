import Goose.Proofs.ConstructionAcceptedScalarWriteFrame

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem AcceptedFrame.bindScalar_update_preservingFuture {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {before after : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame before types) (root : RootInst) (ty : Ty) (value : Value)
    (rootSafe : ∀ id, frame.initialized ≤ id → id < config.module.globals.size → root ≠ .global id)
    (rootType : types root = some ty) (represented : ValueRepresentation ty value)
    (scalar : (∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean)
    (bound : bindRoot root value before = .ok () after) :
    AcceptedFrame config accepted frame after types := by
  have controls : after.nextAct = before.nextAct ∧ after.nextScope = before.nextScope := by
    cases ordinal : before.objectOrdinals.lookup root with
    | none =>
      have exactStep := bindRoot_freshScalar before root value scalar ordinal
      have equal := (ExecutionStep.ok.inj (bound.symm.trans exactStep)).2
      rw [equal]; exact ⟨rfl, rfl⟩
    | some ordinal =>
      simp only [bindRoot, bind, EvalM.get, ordinal, Option.isNone, Bool.false_eq_true, ite_false,
        bindStaticRoot, EvalM.set] at bound
      cases bound; exact ⟨rfl, rfl⟩
  have nonReference : ∀ location, value ≠ .ref location := by
    intro location equal
    rcases scalar with ⟨intTy, number, rfl⟩ | ⟨boolean, rfl⟩ <;> cases equal
  obtain ⟨objectState, objectBound, objects⟩ := bindRoot_objects root value before
  have objectSame := (ExecutionStep.ok.inj (bound.symm.trans objectBound)).2
  subst objectState
  have current : after.objects.lookup root = some value := by simp [objects]
  refine ⟨source.compatible, ?_, ?_, source.initializingBefore, source.aliases, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [controls.1] using source.frontier
  · simpa only [controls.2] using source.scopeFrontier
  · intro id member
    obtain ⟨descriptor, actual, old, declared, resolved, found, valid⟩ := source.locals id member
    by_cases same : actual = root
    · subst actual
      have declaredType := source.localTypes id member descriptor root
        (by simpa only [source.compatible.variables] using declared) resolved
      have typeSame : descriptor.ty = ty := Option.some.inj (declaredType.symm.trans rootType)
      exact ⟨descriptor, root, value, declared, rootOf_transfer frame.interpretation id before after root resolved,
        current, by simpa [typeSame] using represented⟩
    · exact ⟨descriptor, actual, old, declared, rootOf_transfer frame.interpretation id before after actual resolved,
        (bindRoot_lookup_other root actual value before after bound same).trans found, valid⟩
  · intro id member descriptor actual declared resolved
    exact source.localTypes id member descriptor actual declared (rootOf_transfer frame.interpretation id after before actual resolved)
  · intro id condition actual resolved
    have prior := rootOf_transfer frame.interpretation id after before actual resolved
    have different : actual ≠ root := by
      intro same
      subst actual
      have empty := source.uninitializedTypes id condition root prior
      rw [rootType] at empty
      cases empty
    obtain ⟨absent, ordinal⟩ := source.uninitializedLocals id condition actual prior
    exact ⟨(bindRoot_lookup_other root actual value before after bound different).trans absent,
      (bindRoot_ordinals_other root actual value before after bound different).trans ordinal⟩
  · intro id condition actual resolved
    exact source.uninitializedTypes id condition actual (rootOf_transfer frame.interpretation id after before actual resolved)
  · intro id future within
    have different : .global id ≠ root := Ne.symm (rootSafe id future within)
    obtain ⟨absent, ordinal⟩ := source.futureGlobals id future within
    exact ⟨(bindRoot_lookup_other root (.global id) value before after bound different).trans absent,
      (bindRoot_ordinals_other root (.global id) value before after bound different).trans ordinal⟩
  · intro id member actual item resolved found location reference
    have prior := rootOf_transfer frame.interpretation id after before actual resolved
    by_cases same : actual = root
    · subst actual
      have equal : value = item := by simpa [objects] using found
      subst item
      rcases scalar with ⟨intTy, number, rfl⟩ | ⟨boolean, rfl⟩ <;> cases reference
    · have old : before.objects.lookup actual = some item := by
        rw [← bindRoot_lookup_other root actual value before after bound same]; exact found
      exact source.direct id member actual item prior old location reference
  · intro fuel id member roots annotation actual location result resolved found read interior reference
    have prior := rootOf_transfer frame.interpretation id after before actual resolved
    by_cases same : actual = root
    · subst actual
      have equal : value = .ref location := by simpa [objects] using found
      exact (nonReference location equal).elim
    · have old : before.objects.lookup actual = some (.ref location) := by
        rw [← bindRoot_lookup_other root actual value before after bound same]; exact found
      by_cases target : location.root = root
      · have present : after.objects.lookup location.root = some value := by simpa [target] using current
        exact (readLoc_scalarRoot_noReference fuel config.layout after location value result interior scalar present read reference).elim
      · have priorRead := (bindRoot_directReference_read_iff fuel config.layout root value before after location result interior
          bound target reference).mpr read
        exact source.contents fuel id member roots annotation actual location result prior old priorRead interior reference

#print axioms AcceptedFrame.bindScalar_update_preservingFuture
end Goose.Proofs.ConstructionAcceptedExecution
