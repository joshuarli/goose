import Goose.Lower.Validation.SourceReadyOutputTransfers
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes
import Goose.Lower.Validation.SourceStatementTyping

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem scalarLoadedPlace {types : Array (Option VTy)} {typingEnv : TEnv} {results : List Ty}
    {before : LS} {place : Place} {info : PlaceInfo} {integer : IntTy} {start finish : Nat}
    (source : Core.tyPlace typingEnv place start = .ok (info, finish))
    (scalar : info.ty = .int integer) (generated : GeneratedBuilderState before)
    (native :
      let address := lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before
      SummaryPreservation.NativeRows types (Lower.emitDef (.load address.1)
        (lowerEnv typingEnv.mod typingEnv.vars results) address.2).2) :
    let address := lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before
    address.2.cur.isSome = true → valRefLike types address.2.vals.size = false := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let address := lowerPlace place env before
  let loaded := Lower.emitDef (.load address.1) env address.2
  change address.2.cur.isSome = true → valRefLike types address.2.vals.size = false
  intro live
  obtain ⟨mutability, addressType⟩ := lowerPlace_generated_typed place source rfl live generated
  obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
  have loadedLive : loaded.2.cur.isSome = true := by
    simp only [loaded, emitDef_run _ _ current]
    exact live
  have row : types[loaded.1]? = some (some (.data info.ty)) := native.load addressType (show Lower.emitDef (.load address.1) env address.2 = loaded from rfl) loadedLive
  have value : loaded.1 = address.2.vals.size := by simp only [loaded, emitDef_run _ _ current]
  rw [← value]
  simp only [valRefLike, row, VTy.refLike, scalar, Ty.isRefLike]

#print axioms scalarLoadedPlace

end Goose.Lower.Validation.ReplacementContentFlowSource
