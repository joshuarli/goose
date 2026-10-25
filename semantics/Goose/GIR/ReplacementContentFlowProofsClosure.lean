import Goose.GIR.ReplacementContentFlowProofsSupportStart

namespace Goose.GIR.ReplacementContentFlow.Model

inductive ModuleReachable (m : Module) (types : Array (Array (Option VTy))) : Array State → Array State → Prop
  | refl (states : Array State) : ModuleReachable m types states states
  | next {initial current : Array State} : ModuleReachable m types initial current →
      ModuleReachable m types initial (moduleRound m types current)

theorem ModuleReachable.trans {m : Module} {types : Array (Array (Option VTy))}
    {initial middle final : Array State} (first : ModuleReachable m types initial middle)
    (second : ModuleReachable m types middle final) : ModuleReachable m types initial final := by
  induction second with
  | refl => exact first
  | next _ ih => exact ih.next

theorem closeFrom_reachable {m : Module} {types : Array (Array (Option VTy))}
    {fuel : Nat} {initial final : Array State}
    (closed : closeFrom m types fuel initial = some final) : ModuleReachable m types initial final := by
  induction fuel generalizing initial with
  | zero => simp [closeFrom] at closed
  | succ fuel ih =>
    simp only [closeFrom] at closed
    split at closed
    · cases closed; exact .refl _
    · exact (ModuleReachable.next (.refl initial)).trans (ih closed)

theorem close_reachable {m : Module} {types : Array (Array (Option VTy))} {final : Array State}
    (closed : close m types = some final) : ModuleReachable m types (moduleStart m types) final :=
  closeFrom_reachable closed

theorem ModuleReachable.size {m : Module} {types : Array (Array (Option VTy))}
    {initial final : Array State} (initialSize : initial.size = m.funcs.size)
    (reachable : ModuleReachable m types initial final) : final.size = m.funcs.size := by
  cases reachable with
  | refl => exact initialSize
  | next => simp [moduleRound]

theorem ModuleReachable.extends {m : Module} {types : Array (Array (Option VTy))}
    {initial final : Array State} (initialSize : initial.size = m.funcs.size)
    (reachable : ModuleReachable m types initial final) :
    ArrayExtends State.empty State.Extends initial final := by
  induction reachable with
  | refl => exact ArrayExtends.refl _ _ State.Extends.refl _
  | next reachable ih =>
    exact ArrayExtends.trans (relation := State.Extends)
      (fun {_ _ _} left right => left.trans right) ih
      (moduleRound_extends (types := types) (reachable.size initialSize))

theorem close_initial_extends {m : Module} {types : Array (Array (Option VTy))} {final : Array State}
    (closed : close m types = some final) :
    ArrayExtends State.empty State.Extends (moduleStart m types) final :=
  (close_reachable closed).extends (by simp [moduleStart])

theorem moduleRound_fixed_function {m : Module} {types : Array (Array (Option VTy))} {states : Array State}
    (stable : moduleRound m types states = states) (index : Nat) (f : Func) (state : State)
    (functionAt : m.funcs[index]? = some f) (stateAt : states[index]? = some state) :
    round m states f (types[index]?.getD #[]) state = state := by
  have row := congrArg (fun table => table[index]?) stable
  simpa only [moduleRound, Array.getElem?_mapIdx, functionAt, stateAt, Option.map_some,
    Option.getD_some, Option.some.injEq] using row

inductive FunctionReachable (m : Module) (states : Array State) (f : Func) (vt : Array (Option VTy)) :
    State → State → Prop
  | refl (state : State) : FunctionReachable m states f vt state state
  | next {initial current : State} : FunctionReachable m states f vt initial current →
      FunctionReachable m states f vt initial (round m states f vt current)

theorem FunctionReachable.trans {m : Module} {states : Array State} {f : Func} {vt : Array (Option VTy)}
    {initial middle final : State} (first : FunctionReachable m states f vt initial middle)
    (second : FunctionReachable m states f vt middle final) : FunctionReachable m states f vt initial final := by
  induction second with
  | refl => exact first
  | next _ ih => exact ih.next

theorem FunctionReachable.extends {m : Module} {states : Array State} {f : Func} {vt : Array (Option VTy)}
    {initial final : State} (reachable : FunctionReachable m states f vt initial final) : initial.Extends final := by
  induction reachable with
  | refl => exact State.Extends.refl _
  | next _ ih => exact ih.trans (round_extends _ _ _ _ _)

def FunctionFinite (m : Module) (f : Func) (state : State) : Prop :=
  state.Supported (atomUniverse m f) ∧ state.Shape f

theorem FunctionFinite.bounded {m : Module} {f : Func} {state : State}
    (valid : FunctionFinite m f state) : state.Bounded (functionAtomBound m f) := by
  have within := valid.1.bounded
  rwa [atomUniverse_length] at within

theorem FunctionFinite.round {m : Module} {states : Array State} {f : Func} {vt : Array (Option VTy)}
    (inputs : ModuleSupported m states) (addresses : FunctionAddressesBounded m f)
    {state : State} (valid : FunctionFinite m f state) : FunctionFinite m f (round m states f vt state) :=
  ⟨round_supported inputs valid.1 vt addresses.1 addresses.2, (round_extends _ _ _ _ _).shape valid.2⟩

theorem FunctionReachable.finite {m : Module} {states : Array State} {f : Func} {vt : Array (Option VTy)}
    (inputs : ModuleSupported m states) (addresses : FunctionAddressesBounded m f)
    {initial final : State} (valid : FunctionFinite m f initial)
    (reachable : FunctionReachable m states f vt initial final) : FunctionFinite m f final := by
  induction reachable with
  | refl => exact valid
  | next _ ih => exact ih.round inputs addresses

theorem closeFunctionFrom_outcome {m : Module} {states : Array State} {f : Func} {vt : Array (Option VTy)}
    (inputs : ModuleSupported m states) (addresses : FunctionAddressesBounded m f)
    {fuel : Nat} {initial : State} (valid : FunctionFinite m f initial)
    (enough : capacity m f - initial.height (functionAtomBound m f) < fuel) :
    ∃ result, FunctionReachable m states f vt initial result ∧ FunctionFinite m f result ∧
      round m states f vt result = result ∧
      closeFunctionFrom m states f vt fuel initial = if check m f vt result then some result else none := by
  induction fuel generalizing initial with
  | zero => omega
  | succ fuel ih =>
    by_cases stable : round m states f vt initial = initial
    · exact ⟨initial, .refl initial, valid, stable, by simp [closeFunctionFrom, stable]⟩
    · have nextValid := valid.round (vt := vt) inputs addresses
      have growth := (round_extends m states f vt initial).height_lt_of_ne valid.bounded stable
      have limit := State.height_le_capacity (m := m) valid.bounded valid.2
      have nextLimit := State.height_le_capacity (m := m) nextValid.bounded nextValid.2
      change initial.height (functionAtomBound m f) ≤ capacity m f at limit
      change (round m states f vt initial).height (functionAtomBound m f) ≤ capacity m f at nextLimit
      have remaining : capacity m f - (round m states f vt initial).height (functionAtomBound m f) < fuel := by omega
      obtain ⟨result, reachable, finite, fixed, outcome⟩ := ih nextValid remaining
      refine ⟨result, (FunctionReachable.next (.refl initial)).trans reachable, finite, fixed, ?_⟩
      have changed : (round m states f vt initial == initial) = false := by
        apply Bool.eq_false_iff.mpr
        intro equal
        exact stable (eq_of_beq equal)
      simpa only [closeFunctionFrom, changed, Bool.false_eq_true, ite_false] using outcome

theorem closeFunction_outcome (m : Module) (states : Array State) (f : Func) (vt : Array (Option VTy))
    (inputs : ModuleSupported m states) (annotations : annotationsValid m f = true)
    (entryBound : ∀ entry, f.blocks[0]? = some entry → entry.params.length ≤ f.params.length)
    (addresses : FunctionAddressesBounded m f) :
    ∃ result, FunctionReachable m states f vt (start f vt) result ∧ FunctionFinite m f result ∧
      round m states f vt result = result ∧
      closeFunction m states f vt = if check m f vt result then some result else none := by
  exact closeFunctionFrom_outcome inputs addresses
    ⟨start_supported vt annotations entryBound, start_shape f vt⟩ (by omega)

#print axioms ModuleReachable.trans
#print axioms close_reachable
#print axioms close_initial_extends
#print axioms moduleRound_fixed_function
#print axioms FunctionReachable.trans
#print axioms FunctionReachable.extends
#print axioms FunctionReachable.finite
#print axioms closeFunctionFrom_outcome
#print axioms closeFunction_outcome

end Goose.GIR.ReplacementContentFlow.Model
