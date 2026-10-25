import Goose.GIR.ReplacementContentFlowProofsCanonicalReachable

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem normalize_flowAt_bounded {func : Func} {values : Array Roots} {value : ValueId} {roots : List RootRef}
    (known : normalize func (flowAt values value) = some roots) : value < values.size := by
  by_cases bounded : value < values.size
  · exact bounded
  · have absent : values[value]? = none := Array.getElem?_eq_none (Nat.le_of_not_gt bounded)
    simp [flowAt,absent,normalize] at known

theorem State.CanonicalWithin.owner_local {func : Func} {vt : Array (Option VTy)}
    {provenance : Prov} {state : State} {value : ValueId} {mutability : Mutability} {payload : Ty}
    {roots : List RootRef} {slot : SlotId}
    (bounded : state.CanonicalWithin func vt provenance)
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (type : vt[value]? = some (some (.data (.ref mutability payload))))
    (owner : payload.ownerElem?.isSome = true)
    (known : normalize func (flowAt state.values value) = some roots) (member : RootRef.local slot ∈ roots) :
    ∃ storage, func.slots[slot]? = some storage ∧ storage.ty = payload :=
  (bounded.ownerValues value (normalize_flowAt_bounded known) mutability payload type owner).normalizedLocal
    closed known member

end Goose.GIR.ReplacementContentFlow.Model

namespace Goose.GIR

open Goose.Core ReplacementContentFlow.Model

theorem ReplacementContentFlow.forFunction_canonicalWithin {module : Module}
    {provenances : Array Prov} {results : Array (List RootRef)}
    {func : Func} {vt : Array (Option VTy)} {provenance : Prov} {state : State}
    (facts : FunctionCanonicalFacts module func (func.valueTypes module) provenance results)
    (moduleFacts : ModuleCanonicalFacts module (module.funcs.map (·.valueTypes module)) provenances results)
    (annotations : ∀ (index : Nat) (callee : Func), module.funcs[index]? = some callee → annotationsValid module callee = true)
    (entries : ∀ (index : Nat) (callee : Func), module.funcs[index]? = some callee →
      ∀ entry : Block, callee.blocks[0]? = some entry → entry.params.length ≤ callee.params.length)
    (addresses : ∀ (index : Nat) (callee : Func), module.funcs[index]? = some callee → FunctionAddressesBounded module callee)
    (built : ((replacementContentFlow module).forFunction func vt).model = some state) :
    state.CanonicalWithin func (func.valueTypes module) provenance := by
  rw [ReplacementContentFlow.forFunction_model] at built
  split at built
  · cases cached : (replacementContentFlow module).model with
    | none => simp [cached] at built
    | some states =>
        simp only [cached,Option.bind_some] at built
        have closure := (replacementContentFlow_model_checked cached).2.1
        have canonical := close_canonicalWithin moduleFacts annotations entries addresses closure
        exact closeFunction_canonicalWithin facts moduleFacts canonical.1 canonical.2.1 built
  · simp at built

theorem ReplacementContentFlow.forFunction_owner_local {module : Module}
    {provenances : Array Prov} {results : Array (List RootRef)}
    {func : Func} {vt : Array (Option VTy)} {provenance : Prov}
    {value : ValueId} {mutability : Mutability} {payload : Ty} {roots : List RootRef} {slot : SlotId}
    (facts : FunctionCanonicalFacts module func (func.valueTypes module) provenance results)
    (moduleFacts : ModuleCanonicalFacts module (module.funcs.map (·.valueTypes module)) provenances results)
    (annotations : ∀ (index : Nat) (callee : Func), module.funcs[index]? = some callee → annotationsValid module callee = true)
    (entries : ∀ (index : Nat) (callee : Func), module.funcs[index]? = some callee →
      ∀ entry : Block, callee.blocks[0]? = some entry → entry.params.length ≤ callee.params.length)
    (addresses : ∀ (index : Nat) (callee : Func), module.funcs[index]? = some callee → FunctionAddressesBounded module callee)
    (type : (func.valueTypes module)[value]? = some (some (.data (.ref mutability payload))))
    (owner : payload.ownerElem?.isSome = true)
    (known : ((replacementContentFlow module).forFunction func vt).value value = some roots)
    (member : RootRef.local slot ∈ roots) :
    ∃ storage, func.slots[slot]? = some storage ∧ storage.ty = payload := by
  rw [ReplacementFunctionFlow.value_model] at known
  cases built : ((replacementContentFlow module).forFunction func vt).model with
  | none => simp [built] at known
  | some state =>
      simp only [built,Option.bind_some] at known
      exact (forFunction_canonicalWithin facts moduleFacts annotations entries addresses built).owner_local
        facts.roots.closed type owner known member

#print axioms ReplacementContentFlow.forFunction_canonicalWithin
#print axioms ReplacementContentFlow.forFunction_owner_local

end Goose.GIR
