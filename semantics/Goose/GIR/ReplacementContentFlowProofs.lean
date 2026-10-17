import Goose.GIR.ReplacementContentFlow

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem closeFrom_fixed {m : Module} {types : Array (Array (Option VTy))}
    {fuel : Nat} {initial result : Array State}
    (closed : closeFrom m types fuel initial = some result) :
    moduleRound m types result = result := by
  induction fuel generalizing initial with
  | zero => simp [closeFrom] at closed
  | succ fuel ih =>
      simp only [closeFrom] at closed
      split at closed
      · rename_i stable
        cases closed
        exact eq_of_beq stable
      · exact ih closed

theorem close_fixed {m : Module} {types : Array (Array (Option VTy))} {result : Array State}
    (closed : close m types = some result) : moduleRound m types result = result :=
  closeFrom_fixed closed

theorem closeFunctionFrom_fixed_checked {m : Module} {states : Array State} {f : Func}
    {types : Array (Option VTy)} {fuel : Nat} {initial result : State}
    (closed : closeFunctionFrom m states f types fuel initial = some result) :
    round m states f types result = result ∧ check m f types result = true := by
  induction fuel generalizing initial with
  | zero => simp [closeFunctionFrom] at closed
  | succ fuel ih =>
      simp only [closeFunctionFrom] at closed
      split at closed
      · rename_i stable
        split at closed
        · rename_i checked
          cases closed
          exact ⟨eq_of_beq stable, checked⟩
        · simp at closed
      · exact ih closed

theorem closeFunction_fixed_checked {m : Module} {states : Array State} {f : Func}
    {types : Array (Option VTy)} {result : State}
    (closed : closeFunction m states f types = some result) :
    round m states f types result = result ∧ check m f types result = true :=
  closeFunctionFrom_fixed_checked closed

theorem check_writes {m : Module} {f : Func} {types : Array (Option VTy)} {state : State}
    (checked : check m f types state = true) : checkWrites f state = true := by
  simp only [check, Bool.and_eq_true] at checked
  exact checked.1.1.2

theorem check_returned {m : Module} {f : Func} {types : Array (Option VTy)} {state : State}
    (checked : check m f types state = true) : checkReturned f state = true := by
  simp only [check, Bool.and_eq_true] at checked
  exact checked.1.2

theorem check_annotations {m : Module} {f : Func} {types : Array (Option VTy)} {state : State}
    (checked : check m f types state = true) : annotationsValid m f = true := by
  simp only [check, Bool.and_eq_true] at checked
  exact checked.1.1.1.1.2

theorem checkReturned_roots {f : Func} {state : State} {type : Ty} {bound actual : List RootRef}
    (results : f.results = [type]) (reference : type.isRefLike = true)
    (declared : f.roots.results[0]? = some bound) (roots : normalize f state.returned = some actual)
    (checked : checkReturned f state = true) :
    ∀ root ∈ actual, root ∈ bound.flatMap f.expandParameterRoot := by
  simp only [checkReturned, results, reference, ite_true, declared, Option.any_some,
    rootsWithin, roots, Option.any_some] at checked
  intro root member
  exact List.contains_iff_mem.mp (List.all_eq_true.mp checked root member)

theorem closeFrom_success_of_bounded_rank {m : Module} {types : Array (Array (Option VTy))}
    (rank : Array State → Nat) (invariant : Array State → Prop) (bound : Nat)
    (preserved : ∀ state, invariant state → invariant (moduleRound m types state))
    (bounded : ∀ state, invariant state → rank state ≤ bound)
    (progress : ∀ state, invariant state → moduleRound m types state ≠ state →
      rank state < rank (moduleRound m types state))
    {fuel : Nat} {initial : Array State} (valid : invariant initial)
    (enough : bound - rank initial < fuel) :
    ∃ result, closeFrom m types fuel initial = some result := by
  induction fuel generalizing initial with
  | zero => omega
  | succ fuel ih =>
      by_cases stable : moduleRound m types initial = initial
      · exact ⟨initial, by simp [closeFrom, stable]⟩
      · have next := preserved initial valid
        have growth := progress initial valid stable
        have limit := bounded initial valid
        have nextLimit := bounded _ next
        have remaining : bound - rank (moduleRound m types initial) < fuel := by omega
        obtain ⟨result, closed⟩ := ih next remaining
        refine ⟨result, ?_⟩
        have changed : (moduleRound m types initial == initial) = false := by
          apply Bool.eq_false_iff.mpr
          intro equal
          exact stable (eq_of_beq equal)
        simpa only [closeFrom, changed, Bool.false_eq_true, ite_false] using closed

end Goose.GIR.ReplacementContentFlow.Model

namespace Goose.GIR

open ReplacementContentFlow

theorem replacementContentFlow_model_checked {m : Module} {states : Array Model.State}
    (built : (replacementContentFlow m).model = some states) :
    Model.storageClosed m = true ∧
      Model.close m (m.funcs.map (·.valueTypes m)) = some states ∧
      Model.certificate m (m.funcs.map (·.valueTypes m)) states = true ∧
      Model.moduleRound m (m.funcs.map (·.valueTypes m)) states = states := by
  rw [replacementContentFlow_model] at built
  split at built
  · rename_i storage
    cases closed : Model.close m (m.funcs.map (·.valueTypes m)) with
    | none => simp [closed] at built
    | some result =>
        simp only [closed, Option.filter_some] at built
        split at built
        · rename_i certified
          cases built
          exact ⟨storage, rfl, certified, Model.close_fixed closed⟩
        · simp at built
  · simp at built

theorem ReplacementContentFlow.forFunction_model_checked
    {cache : ReplacementContentFlow} {f : Func} {types : Array (Option VTy)} {result : Model.State}
    (built : (cache.forFunction f types).model = some result) :
    types = f.valueTypes cache.source ∧
      ∃ states, cache.model = some states ∧
        Model.round cache.source states f (f.valueTypes cache.source) result = result ∧
        Model.check cache.source f (f.valueTypes cache.source) result = true := by
  rw [ReplacementContentFlow.forFunction_model] at built
  split at built
  · rename_i canonical
    cases model : cache.model with
    | none => simp [model] at built
    | some states =>
        simp only [model, Option.bind_some] at built
        have checked := Model.closeFunction_fixed_checked built
        exact ⟨eq_of_beq canonical, states, rfl, checked⟩
  · simp at built

#print axioms ReplacementContentFlow.Model.check_writes
#print axioms ReplacementContentFlow.Model.check_returned
#print axioms ReplacementContentFlow.Model.check_annotations
#print axioms ReplacementContentFlow.Model.checkReturned_roots
#print axioms ReplacementContentFlow.Model.closeFrom_success_of_bounded_rank
#print axioms replacementContentFlow_source
#print axioms replacementContentFlow_model
#print axioms ReplacementContentFlow.forFunction_model
#print axioms ReplacementFunctionFlow.value_model
#print axioms ReplacementFunctionFlow.contents_model
#print axioms ReplacementFunctionFlow.call_model
#print axioms ReplacementFunctionFlow.mutation_model
#print axioms ReplacementContentFlow.Model.closeFrom_fixed
#print axioms ReplacementContentFlow.Model.close_fixed
#print axioms ReplacementContentFlow.Model.closeFunctionFrom_fixed_checked
#print axioms ReplacementContentFlow.Model.closeFunction_fixed_checked
#print axioms replacementContentFlow_model_checked
#print axioms ReplacementContentFlow.forFunction_model_checked

end Goose.GIR
