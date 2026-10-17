import Goose.Lower.Validation.ReplacementContentFlowSourceReadyCallees
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyEmit

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.callDef {module : GIR.Module} {callees : Array State} {func callee : Func}
    {moduleTypes : Array (Array (Option VTy))} {types calleeTypes : Array (Option VTy)}
    {state effects : State} {completed before after : LS} {env : LEnv}
    {calleeProvenance : Prov} {value : ValueId} {index : FnId} {args : List ValueId} {origin : Option OriginId}
    (frame : SourceReadyFrame module callees func types state completed)
    (closed : close module moduleTypes = some callees)
    (calleeRow : module.funcs[index]? = some callee) (effectRow : callees[index]? = some effects)
    (canonical : effects.CanonicalWithin callee calleeTypes calleeProvenance)
    (parameters : ∀ index root, root ∈ callee.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (run : Lower.emitDef (.call index args origin) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before)
    (resultType : (callee.results = [] ∧ types[value]? = some (some (.data .unit))) ∨
      ∃ type, callee.results = [type] ∧ types[value]? = some (some (.data type)))
    (arguments : before.cur.isSome = true → ∀ (index : Nat) (value : ValueId),
      args[index]? = some value → flowAt state.values value ≠ .pending)
    (contents : before.cur.isSome = true → ∀ (index : Nat) (value : ValueId),
      (callee.roots.contents.find? (·.1 == index)).isSome = true →
      args[index]? = some value → content func state (flowAt state.values value) ≠ .pending) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  apply frame.emitDef run extension allocated bounded
  · intro live operand member
    obtain ⟨position, row⟩ := List.mem_iff_getElem?.mp (show operand ∈ args from member)
    exact arguments live position operand row
  · intro _ address impossible
    cases impossible
  · intro live actualIndex actualArgs actualOrigin same reference
    cases same
    have valueId : value = before.vals.size := by
      cases current : before.cur with
      | none => simp [current] at live
      | some block =>
        have actualRun := run
        rw [emitDef_run _ _ current] at actualRun
        exact (Prod.mk.inj actualRun).1.symm
    rw [← valueId] at reference
    rcases resultType with ⟨empty, typeRow⟩ | ⟨type, single, typeRow⟩
    · simp [valRefLike, typeRow, VTy.refLike, Ty.isRefLike] at reference
    · have resultReference : type.isRefLike = true := by
        simpa only [valRefLike, typeRow, VTy.refLike] using reference
      exact call_result_ready_of_closed_callee closed calleeRow effectRow canonical parameters single resultReference
        (arguments live) (contents live)

#print axioms SourceReadyFrame.callDef

end Goose.Lower.Validation.ReplacementContentFlowSource
