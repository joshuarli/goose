import Goose.GIR.ReplacementContentFlowProofsTouchFootprintSubstitution

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem State.TouchFootprint.step {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)}
    {policy : Atom → Prop} {state : State} {block : Block} {inst : Inst}
    (before : state.TouchFootprint func types policy)
    (canonical : state.CanonicalWithin func types provenance)
    (facts : FunctionCanonicalFacts module func types provenance results)
    (accessed : (∀ value fn args origin, inst ≠ .def value (.call fn args origin)) →
      ∀ source ∈ accessOperands inst, valRefLike types source = true →
      (flowAt state.values source).AtomsWithin (TouchFootprintAtom func policy))
    (backing : ∀ value op, inst = .def value op → ∀ source, BackingOp op source →
      (flowAt state.values source).AtomsWithin (TouchFootprintAtom func policy))
    (global : ∀ index payload kind mutability,
      (module.tyEnv func).globals[index]? = some (payload,kind) →
      wholeOwnerReference (.data (.ref mutability payload)) = false →
      TouchFootprintAtom func policy (.global index))
    (callClosed : ∀ value fn args origin, inst = .def value (.call fn args origin) →
      (step module states func types state inst).TouchFootprint func types policy)
    (blockMember : block ∈ func.blocks.toList) (member : inst ∈ block.insts) :
    (step module states func types state inst).TouchFootprint func types policy := by
  have typed := facts.typing block blockMember inst member
  have uses := facts.uses block blockMember inst member
  cases typed with
  | definition value op type typed valueType =>
      by_cases called : ∃ fn args origin, op = .call fn args origin
      · obtain ⟨fn,args,origin,rfl⟩ := called
        exact callClosed value fn args origin rfl
      · have ordinary : ∀ fn args origin, op ≠ .call fn args origin := by
          intro fn args origin same
          exact called ⟨fn,args,origin,same⟩
        exact before.noncallDefinition canonical facts typed valueType
          (facts.definitions block blockMember value op member) ordinary (backing value op rfl)
          global (accessed (by intro actual fn args origin same; exact ordinary fn args origin (Inst.def.inj same).2)) uses
  | slotInit slot value origin storage row valueType =>
      apply before.addSlot
      intro actual actualAt interior
      have same : actual = storage := Option.some.inj (actualAt.symm.trans row)
      subst actual
      exact before.values value (by rw [canonical.shape.values]; exact uses value (by simp [Inst.uses,Effect.uses]))
        (.data storage.ty) valueType interior
  | store address value origin mutability payload addressType valueType =>
      have exposed := before.touchValues (accessed (by intros; intro same; cases same))
      by_cases reference : payload.isRefLike = true
      · have physical := canonical.holderValues address
          (by rw [canonical.shape.values]; exact uses address (by simp [Inst.uses,Effect.uses]))
          mutability payload addressType reference
        have like : valRefLike types value = true := by simp [valRefLike,valueType,VTy.refLike,reference]
        simpa only [Model.step,Id.run_pure,like,ite_true,touchValues_values] using
          exposed.write facts.roots.parameters physical reference (fun interior =>
            before.values value (by rw [canonical.shape.values]; exact uses value (by simp [Inst.uses,Effect.uses]))
              (.data payload) valueType interior)
      · have like : valRefLike types value = false := by simp [valRefLike,valueType,VTy.refLike,reference]
        simpa only [Model.step,Id.run_pure,like,Bool.false_eq_true,ite_false] using exposed
  | branch target args targetBlock targetAt passing bounds =>
      simpa only [Model.step,Id.run_pure,accessOperands,Model.touchValues,List.foldl_nil] using
        before.edge canonical.shape.values targetAt passing
  | conditional condition thenTarget elseTarget thenArgs elseArgs thenBlock elseBlock thenAt elseAt
      thenTypes elseTypes thenBounds elseBounds =>
      have first := before.edge canonical.shape.values thenAt thenTypes
      have next := first.edge
        ((edge_extends func state thenTarget thenArgs).values.size.symm.trans canonical.shape.values) elseAt elseTypes
      simpa only [Model.step,Id.run_pure,accessOperands,Model.touchValues,List.foldl_nil] using next
  | returned value origin type result valueType =>
      simpa only [Model.step,Id.run_pure,accessOperands,Model.touchValues,List.foldl_nil] using
        before.ret (by rw [canonical.shape.values]; exact uses value (by simp [Inst.uses,Term.uses])) result valueType
  | effect effect ordinary nonstore =>
      have exposed := before.touchValues (accessed (by intros; intro same; cases same))
      cases effect <;> first
        | exact False.elim (ordinary _ _ _ rfl)
        | exact False.elim (nonstore _ _ _ rfl)
        | exact exposed
  | terminal term nonbranch nonconditional nonreturned =>
      cases term with
      | br target args => exact False.elim (nonbranch _ _ rfl)
      | condbr condition left leftArgs right rightArgs => exact False.elim (nonconditional _ _ _ _ _ rfl)
      | ret values origin =>
          cases values with
          | nil => exact before
          | cons value rest =>
              cases rest with
              | nil => exact False.elim (nonreturned _ _ rfl)
              | cons => exact before
      | _ => exact before

#print axioms State.TouchFootprint.step

end Goose.GIR.ReplacementContentFlow.Model
