import Goose.GIR.ReplacementContentFlowProofsSliceCallTransfer

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

def ModuleSliceOrigins (module : Module) (types : Array (Array (Option VTy)))
    (observations : Nat → List Atom) (states : Array State) : Prop :=
  ∀ (index : Nat) (func : Func) (state : State), module.funcs[index]? = some func → states[index]? = some state →
    state.SliceOrigins func (types[index]?.getD #[]) (observations index)

def ModuleObservedTouches (module : Module) (observations : Nat → List Atom) (states : Array State) : Prop :=
  ∀ (index : Nat) (func : Func) (state : State), module.funcs[index]? = some func → states[index]? = some state →
    state.touched = .known (observations index)

theorem State.SliceOrigins.step_closed {module : Module} {states finalStates : Array State}
    {types : Array (Array (Option VTy))} {provenances : Array Prov}
    {func : Func} {localTypes : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)}
    {state final : State} {observed : List Atom} {observations : Nat → List Atom} {block : Block} {inst : Inst}
    (before : state.SliceOrigins func localTypes observed)
    (canonical : state.CanonicalWithin func localTypes provenance)
    (facts : FunctionCanonicalFacts module func localTypes provenance results)
    (moduleFacts : ModuleCanonicalFacts module types provenances results)
    (inputs : ModuleCanonicalWithin module types provenances states) (supported : ModuleSupported module states)
    (inputOrigins : ModuleSliceOrigins module types observations states)
    (finalInputs : ModuleCanonicalWithin module types provenances finalStates)
    (finalSupport : ModuleSupported module finalStates)
    (finalRows : ModuleTouchRows module finalStates)
    (finalTouches : ModuleObservedTouches module observations finalStates)
    (finalCanonical : final.CanonicalWithin func localTypes provenance)
    (growth : state.Extends final) (afterGrowth : (step module states func localTypes state inst).Extends final)
    (fixed : step module finalStates func localTypes final inst = final)
    (touches : final.touched = .known observed)
    (available : ∀ value fn args origin, Inst.def value (.call fn args origin) ∈ block.insts →
      ∀ callee, module.funcs[fn]? = some callee → CallObservationReady callee func final args)
    (blockMember : block ∈ func.blocks.toList) (member : inst ∈ block.insts) :
    (step module states func localTypes state inst).SliceOrigins func localTypes observed := by
  have typed := facts.typing block blockMember inst member
  have uses := facts.uses block blockMember inst member
  cases typed with
  | definition value op type typed valueType =>
      by_cases called : ∃ fn args origin, op = .call fn args origin
      · obtain ⟨fn,args,origin,rfl⟩ := called
        obtain ⟨site⟩ := facts.calls block blockMember value fn args origin member
        obtain ⟨effects,effectsAt,effectsBounded⟩ := inputs.2 fn site.callee site.calleeAt
        obtain ⟨finalEffects,finalEffectsAt,_⟩ := finalInputs.2 fn site.callee site.calleeAt
        exact before.call facts site effectsAt finalEffectsAt effectsBounded
          (inputOrigins fn site.callee effects site.calleeAt effectsAt)
          (supported fn site.callee effects site.calleeAt effectsAt)
          (moduleFacts.functions fn site.callee site.calleeAt).roots finalCanonical
          (finalRows fn site.callee finalEffects site.calleeAt finalEffectsAt)
          (finalSupport fn site.callee finalEffects site.calleeAt finalEffectsAt)
          (finalTouches fn site.callee finalEffects site.calleeAt finalEffectsAt) growth fixed touches
          (available value fn args origin member site.callee site.calleeAt) blockMember member
      · exact before.noncallDefinition canonical facts typed valueType
          (facts.definitions block blockMember value op member)
          (fun fn args origin same => called ⟨fn,args,origin,same⟩) growth afterGrowth fixed touches
  | slotInit slot value origin storage row valueType => exact before.of_components rfl rfl
  | store address value origin mu payload addressType valueType =>
      apply before.of_components
      · simp only [step,Id.run_pure]
        split
        · rw [write_values,touchValues_values]
        · rfl
      · simp only [step,Id.run_pure]
        split
        · rw [write_returned,touchValues_returned]
        · rfl
  | branch target args targetBlock targetAt passing bounds =>
      exact before.edge canonical.shape.values targetAt passing
  | conditional condition thenTarget elseTarget thenArgs elseArgs thenBlock elseBlock thenAt elseAt
      thenTypes elseTypes thenBounds elseBounds =>
      have first := before.edge canonical.shape.values thenAt thenTypes
      exact first.edge ((edge_extends func state thenTarget thenArgs).values.size.symm.trans canonical.shape.values) elseAt elseTypes
  | returned value origin type result valueType =>
      exact before.ret canonical.shape.values (uses value (by simp [Inst.uses,Term.uses])) result valueType
  | effect effect ordinary nonstore =>
      cases effect <;> first
        | exact False.elim (ordinary _ _ _ rfl)
        | exact False.elim (nonstore _ _ _ rfl)
        | exact before.of_components rfl rfl
  | terminal term nonbranch nonconditional nonreturned =>
      cases term with
      | br target args => exact False.elim (nonbranch _ _ rfl)
      | condbr condition left leftArgs right rightArgs => exact False.elim (nonconditional _ _ _ _ _ rfl)
      | ret values origin =>
          cases values with
          | nil => exact before.of_components rfl rfl
          | cons value rest =>
              cases rest with
              | nil => exact False.elim (nonreturned _ _ rfl)
              | cons => exact before.of_components rfl rfl
      | _ => exact before.of_components rfl rfl

#print axioms State.SliceOrigins.step_closed

end Goose.GIR.ReplacementContentFlow.Model
