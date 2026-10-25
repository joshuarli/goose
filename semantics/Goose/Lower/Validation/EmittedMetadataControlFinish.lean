import Goose.Lower.Validation.EmittedMetadataControlBuilder

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem EmittedMetadata.finishFunction {le : LEnv} {before : LS}
    (checked : EmittedMetadata le before) (impl : Core.Impl) (value : ValueId)
    (results : le.results = impl.results.toList)
    (returned : impl.body.value.isSome = true → before.cur.isSome = true →
      TypedValues before impl.results.toList [value])
    (noValue : impl.body.value.isNone = true → impl.results.isEmpty = true ∨
      impl.body.diverges le.mod.noReturn = true) :
    EmittedMetadata le (Goose.Lower.finishFunction impl value le before).2 := by
  have active : Goose.Lower.isLive le before = (before.cur.isSome, before) := by
    simp [Goose.Lower.isLive, bind_run, curBlock_run, pure_run]
  simp only [Goose.Lower.finishFunction, bind_run, read_apply, active]
  by_cases live : before.cur.isSome = true
  · simp only [live, reduceIte]
    by_cases sink : (!impl.results.isEmpty && impl.body.value.isNone && impl.body.diverges le.mod.noReturn) = true
    · simp only [sink, reduceIte, bind_run]
      have allocated := checked.newBlock []
      have closed := allocated.emitTerm (.br before.blocks.size []) (fun _ => .br _ _)
      have selected := closed.setCur (some before.blocks.size)
      have final := selected.emitTerm (.br before.blocks.size []) (fun _ => .br _ _)
      simpa only [newBlock0_run] using final
    · simp only [sink, Bool.false_eq_true, reduceIte]
      apply checked.emitTerm
      intro active
      apply EmittedTermTyped.ret
      rw [results]
      cases bodyValue : impl.body.value with
      | some expr => exact returned (by simp [bodyValue]) live
      | none =>
        have empty : impl.results.isEmpty = true := by
          rcases noValue (by simp [bodyValue]) with empty | diverges
          · exact empty
          · by_cases empty : impl.results.isEmpty = true
            · exact empty
            · exact (sink (by simp [empty, bodyValue, diverges])).elim
        have size : impl.results.size = 0 := by simpa [Array.isEmpty] using empty
        have nil : impl.results.toList = [] := by
          apply List.eq_nil_iff_length_eq_zero.mpr
          simpa only [Array.length_toList] using size
        simpa only [bodyValue, Option.isSome_none, Bool.false_eq_true, reduceIte, nil] using (TypedValues.nil (state := before))
  · simp only [live, Bool.false_eq_true, reduceIte, pure_run]
    exact checked

end Goose.Lower.Validation
