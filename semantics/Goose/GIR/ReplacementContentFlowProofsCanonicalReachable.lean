import Goose.GIR.ReplacementContentFlowProofsCanonicalSteps
import Goose.GIR.ReplacementContentFlowProofsClosure

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem State.CanonicalWithin.round_closed {module : Module} {states : Array State}
    {types : Array (Array (Option VTy))} {provenances : Array Prov}
    {func : Func} {vt : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)} {state : State}
    (before : state.CanonicalWithin func vt provenance)
    (facts : FunctionCanonicalFacts module func vt provenance results)
    (moduleFacts : ModuleCanonicalFacts module types provenances results)
    (inputs : ModuleCanonicalWithin module types provenances states) (supported : ModuleSupported module states) :
    (round module states func vt state).CanonicalWithin func vt provenance := by
  simp only [round,← Array.foldl_toList]
  apply List.foldlRecOn (motive := fun current : State => current.CanonicalWithin func vt provenance)
    func.blocks.toList _ before
  intro current valid block blockMember
  apply List.foldlRecOn (motive := fun current : State => current.CanonicalWithin func vt provenance)
    block.insts _ valid
  intro current valid inst member
  exact valid.step_closed facts moduleFacts inputs supported blockMember member

theorem FunctionReachable.canonicalWithin {module : Module} {states : Array State}
    {types : Array (Array (Option VTy))} {provenances : Array Prov}
    {func : Func} {vt : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)}
    {initial final : State} (reachable : FunctionReachable module states func vt initial final)
    (before : initial.CanonicalWithin func vt provenance)
    (facts : FunctionCanonicalFacts module func vt provenance results)
    (moduleFacts : ModuleCanonicalFacts module types provenances results)
    (inputs : ModuleCanonicalWithin module types provenances states) (supported : ModuleSupported module states) :
    final.CanonicalWithin func vt provenance := by
  induction reachable with
  | refl => exact before
  | next _ ih => exact ih.round_closed facts moduleFacts inputs supported

theorem moduleStart_canonicalWithin {module : Module} {types : Array (Array (Option VTy))}
    {provenances : Array Prov} {results : Array (List RootRef)}
    (facts : ModuleCanonicalFacts module types provenances results) :
    ModuleCanonicalWithin module types provenances (moduleStart module types) := by
  refine ⟨by simp [moduleStart],?_⟩
  intro index func row
  refine ⟨start func (types[index]?.getD #[]),?_,(facts.functions index func row).start⟩
  simp [moduleStart,row]

theorem moduleRound_canonicalWithin {module : Module} {types : Array (Array (Option VTy))}
    {provenances : Array Prov} {results : Array (List RootRef)} {states : Array State}
    (facts : ModuleCanonicalFacts module types provenances results)
    (before : ModuleCanonicalWithin module types provenances states) (supported : ModuleSupported module states) :
    ModuleCanonicalWithin module types provenances (moduleRound module types states) := by
  refine ⟨by simp [moduleRound],?_⟩
  intro index func row
  obtain ⟨state,stateRow,bounded⟩ := before.2 index func row
  refine ⟨round module states func (types[index]?.getD #[]) state,?_,?_⟩
  · simp [moduleRound,row,stateRow]
  · exact bounded.round_closed (facts.functions index func row) facts before supported

theorem ModuleReachable.canonicalWithin {module : Module} {types : Array (Array (Option VTy))}
    {provenances : Array Prov} {results : Array (List RootRef)} {initial final : Array State}
    (reachable : ModuleReachable module types initial final)
    (facts : ModuleCanonicalFacts module types provenances results)
    (before : ModuleCanonicalWithin module types provenances initial) (finite : ModuleFinite module initial)
    (addresses : ∀ (index : Nat) (func : Func), module.funcs[index]? = some func → FunctionAddressesBounded module func) :
    ModuleCanonicalWithin module types provenances final ∧ ModuleFinite module final := by
  induction reachable with
  | refl => exact ⟨before,finite⟩
  | next _ ih =>
      exact ⟨moduleRound_canonicalWithin facts ih.1 ih.2.1,moduleRound_finite addresses ih.2⟩

theorem close_canonicalWithin {module : Module} {types : Array (Array (Option VTy))}
    {provenances : Array Prov} {results : Array (List RootRef)} {final : Array State}
    (facts : ModuleCanonicalFacts module types provenances results)
    (annotations : ∀ (index : Nat) (func : Func), module.funcs[index]? = some func → annotationsValid module func = true)
    (entries : ∀ (index : Nat) (func : Func), module.funcs[index]? = some func →
      ∀ entry : Block, func.blocks[0]? = some entry → entry.params.length ≤ func.params.length)
    (addresses : ∀ (index : Nat) (func : Func), module.funcs[index]? = some func → FunctionAddressesBounded module func)
    (closed : close module types = some final) :
    ModuleCanonicalWithin module types provenances final ∧ ModuleFinite module final :=
  (close_reachable closed).canonicalWithin facts (moduleStart_canonicalWithin facts)
    (moduleStart_finite _ _ annotations entries) addresses

theorem closeFunctionFrom_reachable {module : Module} {states : Array State} {func : Func}
    {vt : Array (Option VTy)} {fuel : Nat} {initial final : State}
    (closed : closeFunctionFrom module states func vt fuel initial = some final) :
    FunctionReachable module states func vt initial final := by
  induction fuel generalizing initial with
  | zero => simp [closeFunctionFrom] at closed
  | succ fuel ih =>
      simp only [closeFunctionFrom] at closed
      split at closed
      · split at closed
        · cases closed; exact .refl _
        · simp at closed
      · exact (FunctionReachable.next (.refl initial)).trans (ih closed)

theorem closeFunction_canonicalWithin {module : Module} {states : Array State}
    {types : Array (Array (Option VTy))} {provenances : Array Prov}
    {func : Func} {vt : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)} {final : State}
    (facts : FunctionCanonicalFacts module func vt provenance results)
    (moduleFacts : ModuleCanonicalFacts module types provenances results)
    (inputs : ModuleCanonicalWithin module types provenances states) (supported : ModuleSupported module states)
    (closed : closeFunction module states func vt = some final) : final.CanonicalWithin func vt provenance :=
  (closeFunctionFrom_reachable closed).canonicalWithin facts.start facts moduleFacts inputs supported

#print axioms State.CanonicalWithin.round_closed
#print axioms FunctionReachable.canonicalWithin
#print axioms ModuleReachable.canonicalWithin
#print axioms close_canonicalWithin
#print axioms closeFunction_canonicalWithin

end Goose.GIR.ReplacementContentFlow.Model
