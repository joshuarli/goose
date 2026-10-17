import Goose.GIR.ReplacementContentFlowProofsSliceTouches

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem accessOperands_uses (inst : Inst) : accessOperands inst ⊆ inst.uses := by
  cases inst with
  | «def» value op => cases op <;> simp [accessOperands]
  | eff effect => cases effect <;> simp [accessOperands,Inst.uses,Effect.uses]
  | term term => simp [accessOperands]

theorem edge_touched_of_block {func : Func} {state : State} {target : BlockId} {args : List ValueId}
    {block : Block} (row : func.blocks[target]? = some block) :
    (edge func state target args).touched = state.touched := by
  simp only [edge,row]
  apply List.foldlRecOn (motive := fun current : State => current.touched = state.touched)
    (block.params.zip args) _ rfl
  intro current valid pair _
  exact valid

theorem State.CanonicalWithin.step_touchRows {module : Module} {states : Array State}
    {types : Array (Array (Option VTy))} {provenances : Array Prov}
    {func : Func} {vt : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)}
    {state : State} {block : Block} {inst : Inst}
    (before : state.CanonicalWithin func vt provenance)
    (facts : FunctionCanonicalFacts module func vt provenance results)
    (moduleFacts : ModuleCanonicalFacts module types provenances results)
    (inputs : ModuleCanonicalWithin module types provenances states)
    (supported : ModuleSupported module states)
    (touched : state.touched.AtomsWithin (fun atom => (normalizeAtom func atom).isSome = true))
    (inputTouched : ∀ (index : Nat) (callee : Func) (effects : State), module.funcs[index]? = some callee → states[index]? = some effects →
      effects.touched.AtomsWithin (fun atom => (normalizeAtom callee atom).isSome = true))
    (blockMember : block ∈ func.blocks.toList) (member : inst ∈ block.insts) :
    (step module states func vt state inst).touched.AtomsWithin
      (fun atom => (normalizeAtom func atom).isSome = true) := by
  have uses := facts.uses block blockMember inst member
  have accessReady : (Model.touchValues vt state (accessOperands inst)).touched.AtomsWithin
      (fun atom => (normalizeAtom func atom).isSome = true) := by
    apply touchValues_normalizableAtoms touched
    intro value accessed _
    exact (before.values value (by rw [before.shape.values]; exact uses value (accessOperands_uses inst accessed))).normalizableAtoms
  have after := before.step_closed facts moduleFacts inputs supported blockMember member
  have typed := facts.typing block blockMember inst member
  cases typed with
  | definition value op type typed canonical =>
      by_cases called : ∃ fn args origin, op = .call fn args origin
      · obtain ⟨fn,args,origin,rfl⟩ := called
        obtain ⟨site⟩ := facts.calls block blockMember value fn args origin member
        obtain ⟨effects,effectsAt,_⟩ := inputs.2 fn site.callee site.calleeAt
        have next := before.callTouched_normalizableAtoms
          facts site (moduleFacts.functions fn site.callee site.calleeAt).roots effectsAt
          (supported fn site.callee effects site.calleeAt effectsAt) touched
          (inputTouched fn site.callee effects site.calleeAt effectsAt) blockMember member
        simpa only [step,Id.run_pure,interiorLoadedResults,loadedResults,List.filter_nil,Model.touchValues,List.foldl_nil] using next
      · have ordinary : ∀ fn args origin, op ≠ .call fn args origin := by
          intro fn args origin same
          exact called ⟨fn,args,origin,same⟩
        rw [step_def_noncall _ _ _ _ _ _ _ ordinary] at after ⊢
        let exposed := Model.touchValues vt state (accessOperands (.def value op))
        let produced : State := { exposed with values := addFlow exposed.values value (result func vt exposed value op) }
        change (Model.touchValues vt produced (interiorLoadedResults vt (.def value op))).touched.AtomsWithin _
        apply touchValues_normalizableAtoms (state := produced) accessReady
        intro source loaded _
        have same : source = value := by
          have loaded := (List.mem_filter.mp loaded).1
          cases op <;> simp_all [loadedResults]
        subst source
        exact (after.values value (by rw [after.shape.values]; exact facts.definitions block blockMember value op member)).normalizableAtoms
  | slotInit slot value origin storage row canonical => exact accessReady
  | store address value origin mu payload addressType valueType =>
      have valueBound : value < state.values.size := by
        rw [before.shape.values]
        exact uses value (by simp [Inst.uses,Effect.uses])
      have addressBound : address < state.values.size := by
        rw [before.shape.values]
        exact uses address (by simp [Inst.uses,Effect.uses])
      by_cases reference : payload.isRefLike = true
      · have physical := before.holderValues address addressBound mu payload addressType reference
        have flag : valRefLike vt value = true := by simp [valRefLike,valueType,VTy.refLike,reference]
        simpa only [step,Id.run_pure,flag,ite_true,HolderRoots.write_touched physical,touchValues_values] using accessReady
      · have flag : valRefLike vt value = false := by simp [valRefLike,valueType,VTy.refLike,reference]
        simpa only [step,Id.run_pure,flag,Bool.false_eq_true,ite_false] using accessReady
  | branch target args targetBlock targetAt types bounds =>
      simpa only [step,Id.run_pure,edge_touched_of_block targetAt] using accessReady
  | conditional condition thenTarget elseTarget thenArgs elseArgs thenBlock elseBlock thenAt elseAt
      thenTypes elseTypes thenBounds elseBounds =>
      simpa only [step,Id.run_pure,edge_touched_of_block thenAt,edge_touched_of_block elseAt] using accessReady
  | returned value origin type result canonical => exact accessReady
  | effect effect ordinary nonstore =>
      cases effect <;> first
        | exact False.elim (ordinary _ _ _ rfl)
        | exact False.elim (nonstore _ _ _ rfl)
        | exact accessReady
  | terminal term nonbranch nonconditional nonreturned =>
      cases term with
      | br target args => exact False.elim (nonbranch _ _ rfl)
      | condbr condition left leftArgs right rightArgs => exact False.elim (nonconditional _ _ _ _ _ rfl)
      | ret values origin =>
          cases values with
          | nil => exact accessReady
          | cons value rest =>
              cases rest with
              | nil => exact False.elim (nonreturned _ _ rfl)
              | cons => exact accessReady
      | _ => exact accessReady

#print axioms State.CanonicalWithin.step_touchRows

end Goose.GIR.ReplacementContentFlow.Model
