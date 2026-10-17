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
