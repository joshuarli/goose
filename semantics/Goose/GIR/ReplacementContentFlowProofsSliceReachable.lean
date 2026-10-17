import Goose.GIR.ReplacementContentFlowProofsSliceSteps

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem state_foldl_below {α : Type} (values : List α) (update : State → α → State)
    (growth : ∀ (state : State) (value : α), state.Extends (update state value)) (predicate : State → Prop)
    (preserved : ∀ (current : State) (value : α), value ∈ values → current.Extends final → (update current value).Extends final →
      predicate current → predicate (update current value))
    (initial : State) (below : (values.foldl update initial).Extends final) (valid : predicate initial) :
    predicate (values.foldl update initial) := by
  induction values generalizing initial with
  | nil => exact valid
  | cons value rest ih =>
      have nextBelow := (state_foldl_extends rest update growth (update initial value)).trans below
      have beforeBelow := (growth initial value).trans nextBelow
      have next := preserved initial value (by simp) beforeBelow nextBelow valid
      exact ih (fun current next member => preserved current next (List.mem_cons_of_mem _ member))
        (update initial value) below next

theorem State.SliceOrigins.round_closed {module : Module} {states finalStates : Array State}
    {types : Array (Array (Option VTy))} {provenances : Array Prov}
    {func : Func} {localTypes : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)}
    {state final : State} {observed : List Atom} {observations : Nat → List Atom}
    (before : state.SliceOrigins func localTypes observed)
    (canonical : state.CanonicalWithin func localTypes provenance)
    (facts : FunctionCanonicalFacts module func localTypes provenance results)
    (moduleFacts : ModuleCanonicalFacts module types provenances results)
    (inputs : ModuleCanonicalWithin module types provenances states) (supported : ModuleSupported module states)
    (inputOrigins : ModuleSliceOrigins module types observations states)
    (finalInputs : ModuleCanonicalWithin module types provenances finalStates)
    (finalSupport : ModuleSupported module finalStates) (finalRows : ModuleTouchRows module finalStates)
    (finalTouches : ModuleObservedTouches module observations finalStates)
    (finalCanonical : final.CanonicalWithin func localTypes provenance)
    (afterGrowth : (round module states func localTypes state).Extends final)
    (fixed : round module finalStates func localTypes final = final)
    (touches : final.touched = .known observed)
    (available : ∀ block ∈ func.blocks.toList, ∀ value fn args origin,
      Inst.def value (.call fn args origin) ∈ block.insts →
      ∀ callee, module.funcs[fn]? = some callee → CallObservationReady callee func final args) :
    (round module states func localTypes state).SliceOrigins func localTypes observed := by
  have output : (round module states func localTypes state).SliceOrigins func localTypes observed ∧
      (round module states func localTypes state).CanonicalWithin func localTypes provenance := by
    simp only [round,← Array.foldl_toList] at afterGrowth ⊢
    apply state_foldl_below func.blocks.toList _
      (fun current block => state_foldl_extends block.insts _ (step_extends module states func localTypes) current)
      (fun current => current.SliceOrigins func localTypes observed ∧ current.CanonicalWithin func localTypes provenance)
      ?_ state afterGrowth ⟨before,canonical⟩
    intro current block blockMember beforeBelow blockBelow valid
    apply state_foldl_below block.insts _ (step_extends module states func localTypes)
      (fun current => current.SliceOrigins func localTypes observed ∧ current.CanonicalWithin func localTypes provenance)
      ?_ current blockBelow valid
    intro current inst member beforeBelow afterBelow valid
    exact ⟨valid.1.step_closed valid.2 facts moduleFacts inputs supported inputOrigins finalInputs finalSupport
        finalRows finalTouches finalCanonical beforeBelow afterBelow
        (round_fixed_step module finalStates func localTypes final fixed block blockMember inst member)
        touches (available block blockMember) blockMember member,
      valid.2.step_closed facts moduleFacts inputs supported blockMember member⟩
  exact output.1

def moduleTouchAtoms (states : Array State) (index : Nat) : List Atom :=
  match states[index]? with
  | some state => match state.touched with
    | .known atoms => atoms
    | _ => []
  | none => []

theorem ModuleReachable.observedTouches {module : Module} {types : Array (Array (Option VTy))}
    {provenances : Array Prov} {results : Array (List RootRef)} {final : Array State}
    (reachable : ModuleReachable module types (moduleStart module types) final)
    (facts : ModuleCanonicalFacts module types provenances results)
    (finite : ModuleFinite module (moduleStart module types))
    (addresses : ∀ (index : Nat) (func : Func), module.funcs[index]? = some func → FunctionAddressesBounded module func) :
    ModuleObservedTouches module (moduleTouchAtoms final) final := by
  have rows := reachable.touchRows facts (moduleStart_canonicalWithin facts) finite addresses (moduleStart_touchRows _ _)
  have growth := reachable.extends (by simp [moduleStart])
  intro index func state funcAt stateAt
  have normalizable := rows index func state funcAt stateAt
  have initialAt : (moduleStart module types)[index]? = some (start func (types[index]?.getD #[])) := by
    simp [moduleStart,funcAt]
  have touchedGrowth := (growth.values index).touched
  simp only [initialAt,stateAt,Option.getD_some] at touchedGrowth
  cases touchedAt : state.touched with
  | pending =>
      rw [touchedAt] at touchedGrowth
      rw [start_components] at touchedGrowth
      exact False.elim touchedGrowth
  | unknown => rw [touchedAt] at normalizable; exact False.elim normalizable
  | known atoms => simp [moduleTouchAtoms,stateAt,touchedAt]

theorem moduleStart_sliceOrigins (module : Module) (types : Array (Array (Option VTy)))
    (observations : Nat → List Atom) {provenances : Array Prov} {results : Array (List RootRef)}
    (facts : ModuleCanonicalFacts module types provenances results) :
    ModuleSliceOrigins module types observations (moduleStart module types) := by
  intro index func state funcAt stateAt
  have same : state = start func (types[index]?.getD #[]) := by
    simpa [moduleStart,funcAt] using stateAt.symm
  subst state
  exact start_sliceOrigins _ (facts.functions index func funcAt)

theorem ModuleReachable.sliceOrigins {module : Module} {types : Array (Array (Option VTy))}
    {provenances : Array Prov} {results : Array (List RootRef)} {current final : Array State}
    (reachable : ModuleReachable module types (moduleStart module types) current)
    (suffix : ModuleReachable module types current final)
    (facts : ModuleCanonicalFacts module types provenances results)
    (finite : ModuleFinite module (moduleStart module types))
    (addresses : ∀ (index : Nat) (func : Func), module.funcs[index]? = some func → FunctionAddressesBounded module func)
    (fixed : moduleRound module types final = final)
    (available : ∀ (index : Nat) (func : Func) (state : State), module.funcs[index]? = some func → final[index]? = some state →
      ∀ block ∈ func.blocks.toList, ∀ value fn args origin, Inst.def value (.call fn args origin) ∈ block.insts →
        ∀ callee, module.funcs[fn]? = some callee → CallObservationReady callee func state args) :
    ModuleSliceOrigins module types (moduleTouchAtoms final) current := by
  induction reachable with
  | refl => exact moduleStart_sliceOrigins _ _ _ facts
  | @next current reachable ih =>
      have currentSuffix := (ModuleReachable.next (.refl current)).trans suffix
      have earlier := ih currentSuffix
      have allReachable := reachable.trans currentSuffix
      have finalTouches := allReachable.observedTouches facts finite addresses
      have finalRows := allReachable.touchRows facts (moduleStart_canonicalWithin facts) finite addresses (moduleStart_touchRows _ _)
      obtain ⟨finalCanonical,finalFinite⟩ := allReachable.canonicalWithin facts (moduleStart_canonicalWithin facts) finite addresses
      obtain ⟨currentCanonical,currentFinite⟩ := reachable.canonicalWithin facts (moduleStart_canonicalWithin facts) finite addresses
      have below := suffix.extends (by simp [moduleRound])
      intro index func state funcAt stateAt
      obtain ⟨before,beforeAt,beforeBound⟩ := currentCanonical.2 index func funcAt
      obtain ⟨after,afterAt,afterBound⟩ := finalCanonical.2 index func funcAt
      have produced : (moduleRound module types current)[index]? =
          some (round module current func (types[index]?.getD #[]) before) := by
        simp [moduleRound,funcAt,beforeAt]
      have same : state = round module current func (types[index]?.getD #[]) before :=
        Option.some.inj (stateAt.symm.trans produced)
      subst state
      have afterBelow := below.values index
      simp only [produced,afterAt,Option.getD_some] at afterBelow
      exact (earlier index func before funcAt beforeAt).round_closed beforeBound (facts.functions index func funcAt) facts
        currentCanonical currentFinite.1 earlier finalCanonical finalFinite.1 finalRows finalTouches afterBound afterBelow
        (moduleRound_fixed_function fixed index func after funcAt afterAt)
        (finalTouches index func after funcAt afterAt) (available index func after funcAt afterAt)

theorem close_sliceOrigins {module : Module} {types : Array (Array (Option VTy))}
    {provenances : Array Prov} {results : Array (List RootRef)} {final : Array State}
    (facts : ModuleCanonicalFacts module types provenances results)
    (annotations : ∀ (index : Nat) (func : Func), module.funcs[index]? = some func → annotationsValid module func = true)
    (entries : ∀ (index : Nat) (func : Func), module.funcs[index]? = some func →
      ∀ entry : Block, func.blocks[0]? = some entry → entry.params.length ≤ func.params.length)
    (addresses : ∀ (index : Nat) (func : Func), module.funcs[index]? = some func → FunctionAddressesBounded module func)
    (closed : close module types = some final)
    (available : ∀ (index : Nat) (func : Func) (state : State), module.funcs[index]? = some func → final[index]? = some state →
      ∀ block ∈ func.blocks.toList, ∀ value fn args origin, Inst.def value (.call fn args origin) ∈ block.insts →
        ∀ callee, module.funcs[fn]? = some callee → CallObservationReady callee func state args) :
    ModuleSliceOrigins module types (moduleTouchAtoms final) final :=
  (close_reachable closed).sliceOrigins (.refl final) facts (moduleStart_finite _ _ annotations entries)
    addresses (close_fixed closed) available

#print axioms State.SliceOrigins.round_closed
#print axioms ModuleReachable.sliceOrigins
#print axioms close_sliceOrigins

end Goose.GIR.ReplacementContentFlow.Model
