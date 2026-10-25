import Goose.Proofs.ExitExecutionStorageIntervals

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem variableElement_no_fixedSize (layout : LayoutEnv) (ty : Ty)
    (varying : ty.variableElement = true) : fixedByteSize? layout ty = none := by
  cases ty <;> try cases varying
  case varr element => rfl
  case arr element count =>
    simp only [Ty.variableElement] at varying
    simp only [fixedByteSize?, variableElement_no_fixedSize layout element varying, Option.map_none]
termination_by sizeOf ty

theorem nonfixed_no_fixedSize (layout : LayoutEnv) (ty : Ty)
    (nonfixed : ty.nonfixed = true) : fixedByteSize? layout ty = none := by
  cases ty <;> try cases nonfixed
  all_goals try rfl
  case arr element count =>
    simp only [Ty.nonfixed] at nonfixed
    simp only [fixedByteSize?, variableElement_no_fixedSize layout element nonfixed, Option.map_none]

theorem packedEnd_sampled_run_backing (fuel : Nat) (layout : LayoutEnv) (ty : Ty)
    (bytes : ByteArray) (start finish : Nat) (run : SampledRun)
    (nonfixed : ty.nonfixed = true)
    (scanned : packedEnd fuel layout ty bytes start = .ok finish)
    (sampled : samplePacked ty bytes start = .ok run) :
    ∃ backingFuel, elementsEnd backingFuel layout run.element run.count bytes run.byteStart = .ok finish := by
  have size := nonfixed_no_fixedSize layout ty nonfixed
  cases fuel with
  | zero => cases scanned
  | succ fuel =>
    simp only [packedEnd, size] at scanned
    cases ty <;> try (solve | cases sampled)
    case arr element count =>
      cases sampled
      exact ⟨fuel, scanned⟩
    case varr element =>
      cases counted : readCount bytes start with
      | error reason => simp only [samplePacked, counted, bind, Except.bind] at sampled; cases sampled
      | ok count =>
        simp only [samplePacked, counted, bind, Except.bind] at sampled
        cases sampled
        simp only [counted, bind, Except.bind] at scanned
        exact ⟨fuel, scanned⟩

theorem samplePacked_start_bound (ty : Ty) (bytes : ByteArray) (start : Nat) (run : SampledRun)
    (sampled : samplePacked ty bytes start = .ok run) : start ≤ run.byteStart := by
  cases ty <;> try (solve | cases sampled)
  case arr element count => cases sampled; exact Nat.le_refl _
  case varr element =>
    cases counted : readCount bytes start with
    | error reason => simp only [samplePacked, counted, bind, Except.bind] at sampled; cases sampled
    | ok count =>
      simp only [samplePacked, counted, bind, Except.bind] at sampled
      cases sampled
      simp only
      omega

#print axioms nonfixed_no_fixedSize
#print axioms packedEnd_sampled_run_backing
#print axioms samplePacked_start_bound

end Goose.Proofs.ExitExecution
