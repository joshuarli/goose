import Goose.Lower.Validation.SourceReadyTypedStatementsRange
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyReferences
import Goose.Lower.Validation.SourceReadable

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem ready_def_current (operation : Op) (env : LEnv) (before : LS) :
    (Lower.emitDef operation env before).2.cur = before.cur := by
  cases current : before.cur with
  | none => rw [emitDef_none _ _ current]; exact current
  | some block => rw [emitDef_run _ _ current]; exact current

theorem ready_borrow_current (mutability : Mutability) (address : ValueId) (env : LEnv) (before : LS) :
    (Lower.borrowTo mutability address env before).2.cur = before.cur := by
  rcases borrowTo_cases (show Lower.borrowTo mutability address env before =
      Lower.borrowTo mutability address env before from rfl) with frozen | borrowed
  · rcases freezeTo_cases frozen with ⟨_, same⟩ | emitted
    · exact congrArg LS.cur same
    · have equal := congrArg (fun result => result.2.cur) emitted
      exact equal.symm.trans (ready_def_current _ _ _)
  · have equal := congrArg (fun result => result.2.cur) borrowed
    exact equal.symm.trans (ready_def_current _ _ _)

theorem ready_eachElem_current (slot : VarId) (byReference : Bool) (address : ValueId) (env : LEnv) (before : LS) :
    (Lower.eachElemValue slot byReference address env before).2.cur = before.cur := by
  cases byReference with
  | false => exact ready_def_current _ _ _
  | true =>
    simp only [Lower.eachElemValue, reduceIte, bind_run, read_apply]
    cases row : env.vars[slot]? with
    | none => rfl
    | some localVar =>
      simp only
      cases shape : localVar.ty <;> simp only [shape]
      all_goals first | rfl | exact ready_borrow_current _ _ _ _

theorem SourceReadyFrame.eachElemValue {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS} {env : LEnv}
    {slot : VarId} {byReference : Bool} {address : ValueId} {element : Ty}
    (frame : SourceReadyFrame module callees func types state completed)
    (extension : (Lower.eachElemValue slot byReference address env before).2.Ext completed)
    (allocated : (Lower.eachElemValue slot byReference address env before).2.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before)
    (native : SummaryPreservation.NativeRows types (Lower.eachElemValue slot byReference address env before).2)
    (flat : element.flat = true)
    (typed : before.cur.isSome = true → ∃ mu, before.vals[address]? = some (some (.data (.ref mu element))))
    (available : before.cur.isSome = true → flowAt state.values address ≠ .pending) :
    ValueReadyAt state (Lower.eachElemValue slot byReference address) env before := by
  unfold ValueReadyAt
  cases byReference with
  | false =>
    exact frame.emitDef rfl extension allocated bounded (by
      intro live operand member
      have same : operand = address := by simpa [Op.uses] using member
      subst operand
      exact available live) (by
        intro live selected same reference
        obtain ⟨mu, addressType⟩ := typed live
        let loaded := Lower.emitDef (.load address) env before
        have outputLive : loaded.2.cur.isSome = true := by rw [ready_def_current]; exact live
        have outputType : types[loaded.1]? = some (some (.data element)) := native.load addressType rfl outputLive
        obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
        have id : loaded.1 = before.vals.size := by simp only [loaded, emitDef_run _ _ current]
        have scalar : valRefLike types loaded.1 = false := by
          have nonref : element.isRefLike = false := by cases element <;> simp_all [Ty.flat, Ty.isRefLike]
          simp only [valRefLike, outputType, VTy.refLike, nonref]
        rw [id] at scalar
        rw [scalar] at reference
        contradiction)
      (by intro _ fn args origin impossible; cases impossible)
  | true =>
    simp only [Lower.eachElemValue, reduceIte, bind_run, read_apply] at extension allocated native ⊢
    cases row : env.vars[slot]? with
    | none =>
      simp only [row, pure_run] at extension allocated native ⊢
      exact ⟨.refl _ _, available⟩
    | some localVar =>
      simp only [row] at extension allocated native ⊢
      cases shape : localVar.ty <;> simp only [shape] at extension allocated native ⊢
      all_goals first
        | exact ⟨.refl _ _, available⟩
        | exact frame.borrowTo rfl extension allocated bounded available

end Goose.Lower.Validation.ReplacementContentFlowSource
