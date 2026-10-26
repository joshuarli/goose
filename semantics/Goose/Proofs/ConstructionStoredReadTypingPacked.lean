import Goose.Proofs.ConstructionStoredReadTypingFixed
import Goose.Proofs.ExitExecutionStoredChildBacking

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ExitExecution

private theorem samplePacked_detached_backing (fuel : Nat) (layout : LayoutEnv) (state : ExecutionState)
    (id start finish : Nat) (ty : Ty) (storage : ReceivingStorage) (run : SampledRun)
    (object : Option Nat) (path : List Nat)
    (present : state.construction.storage[id]? = some storage)
    (varying : ty.nonfixed = true)
    (scanned : packedEnd fuel layout ty storage.bytes start = .ok finish)
    (sampled : samplePacked ty storage.bytes start = .ok run)
    (upper : finish ≤ storage.bytes.size) :
    StoredValueBacking layout state ⟨id, start, ty, run.count, none, object, path, run.count⟩ := by
  obtain ⟨backingFuel, measured⟩ := packedEnd_sampled_run_backing fuel layout ty storage.bytes start finish run varying scanned sampled
  have lower := elementsEnd_monotone backingFuel layout run.element run.count storage.bytes run.byteStart finish measured
  cases ty <;> try (solve | cases sampled)
  case arr element count =>
    cases sampled
    exact .detached storage element present rfl rfl ⟨backingFuel, finish, measured, lower, upper⟩
  case varr element =>
    cases counted : readCount storage.bytes start with
    | error reason => simp only [samplePacked, counted, bind, Except.bind] at sampled; cases sampled
    | ok count =>
      simp only [samplePacked, counted, bind, Except.bind] at sampled
      cases sampled
      exact .detached storage element present rfl rfl ⟨backingFuel, finish, measured, lower, upper⟩

private theorem storedBacking_sampled_typed (layout : LayoutEnv) (state : ExecutionState) (stored : StoredValue)
    (backed : StoredValueBacking layout state stored) :
    ∃ storage run, state.construction.storage[stored.storage]? = some storage ∧
      sampledStored stored state = .ok (storage.bytes, run) state ∧
      SampledRunBacking layout storage.bytes (storedWrittenRun stored run) ∧
      elementType stored.ty = some run.element := by
  cases backed with
  | detached storage element present detached type interval =>
    refine ⟨storage, _, present, ?_, interval, type⟩
    simp only [sampledStored, getStorage, EvalM.get, bind, present, pure, detached, type]
    rfl
  | named id storage destination count present named binding backing type start progress element elementType interval =>
    refine ⟨storage, _, present, ?_, interval, elementType⟩
    cases current : destination.progress <;>
      simp_all only [sampledStored, getStorage, getDestination, EvalM.get, bind, pure,
        progressCount, Option.some.injEq]

private theorem readStoredElement_nonfixed (fuel : Nat) (layout : LayoutEnv) (types : RootTypes)
    (state after : ExecutionState) (stored : StoredValue) (index : Nat) (element : Ty) (value : Value)
    (backed : StoredValueBacking layout state stored) (sequence : elementType stored.ty = some element)
    (varying : element.nonfixed = true)
    (executed : readStoredElement fuel layout stored index state = .ok value after) :
    after = state ∧ ValueRepresentation element value ∧ PointerTypedValue types element value ∧
      ValueStorageBacked layout state value := by
  obtain ⟨storage, sampledRun, present, sampled, interval, elementType⟩ :=
    storedBacking_sampled_typed layout state stored backed
  have sameElement : sampledRun.element = element := Option.some.inj (elementType.symm.trans sequence)
  let run := storedWrittenRun stored sampledRun
  have runElement : run.element = element := sameElement
  have pathRun : storedPathRun stored state = .ok (storage.bytes, run) state := by
    simp only [storedPathRun, sampled, bind, pure]
    rfl
  simp only [readStoredElement, pathRun, bind] at executed
  cases selected : elementInterval fuel layout storage.bytes run index with
  | error reason =>
    cases reason <;> simp only [selected, liftLayout, fault, timeout, EvalM.stop] at executed <;> cases executed
  | ok pair =>
    obtain ⟨start, finish⟩ := pair
    simp only [selected, liftLayout, pure, runElement, varying, ↓reduceIte] at executed
    cases child : samplePacked element storage.bytes start with
    | error reason =>
      cases reason <;> simp only [child, fault, timeout, EvalM.stop] at executed <;> cases executed
    | ok childRun =>
      simp only [child] at executed
      cases executed
      refine ⟨rfl, .stored element _ varying rfl, .stored element _, .stored _ ?_⟩
      obtain ⟨backingFuel, endByte, measured, lower, upper⟩ := interval.interval
      have inside := elementInterval_within_run fuel backingFuel layout storage.bytes run index start finish endByte selected measured
      have childScan := (elementInterval_result_inv fuel layout storage.bytes run index start finish selected).2.2
      rw [runElement] at childScan
      exact samplePacked_detached_backing fuel layout state stored.storage start finish element storage childRun
        _ _ present varying childScan child (Nat.le_trans inside upper)

theorem readStoredElement_typed (fuel : Nat) (layout : LayoutEnv) (types : RootTypes)
    (state after : ExecutionState) (stored : StoredValue) (index : Nat) (element : Ty) (value : Value)
    (backed : StoredValueBacking layout state stored) (sequence : elementType stored.ty = some element)
    (conforms : LayoutConforms layout element)
    (executed : readStoredElement fuel layout stored index state = .ok value after) :
    after = state ∧ ValueRepresentation element value ∧ PointerTypedValue types element value ∧
      ValueStorageBacked layout state value := by
  by_cases varying : element.nonfixed = true
  · exact readStoredElement_nonfixed fuel layout types state after stored index element value backed sequence varying executed
  · have inline : element.nonfixed = false := Bool.eq_false_iff.mpr varying
    obtain ⟨storage, sampledRun, present, sampled, interval, elementType⟩ :=
      storedBacking_sampled_typed layout state stored backed
    have sameElement : sampledRun.element = element := Option.some.inj (elementType.symm.trans sequence)
    let run := storedWrittenRun stored sampledRun
    have runElement : run.element = element := sameElement
    have pathRun : storedPathRun stored state = .ok (storage.bytes, run) state := by
      simp only [storedPathRun, sampled, bind, pure]
      rfl
    simp only [readStoredElement, pathRun, bind] at executed
    cases selected : elementInterval fuel layout storage.bytes run index with
    | error reason =>
      cases reason <;> simp only [selected, liftLayout, fault, timeout, EvalM.stop] at executed <;> cases executed
    | ok pair =>
      obtain ⟨start, finish⟩ := pair
      simp only [selected, liftLayout, pure, runElement, inline, Bool.false_eq_true, ↓reduceIte] at executed
      cases decoded : fixedValue fuel layout element storage.bytes start with
      | error reason => simp only [decoded, Goose.Construct.liftExcept, EvalM.stop] at executed; cases executed
      | ok child =>
        simp only [decoded, Goose.Construct.liftExcept, pure] at executed
        cases executed
        exact ⟨rfl, fixedValue_typed fuel layout types state element storage.bytes start _ conforms decoded⟩

#print axioms readStoredElement_typed

end Goose.Proofs.ConstructionAcceptedExecution
