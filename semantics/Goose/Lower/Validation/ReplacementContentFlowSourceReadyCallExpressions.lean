import Goose.Lower.Validation.ReplacementContentFlowSourceReadyCallDefinitions
import Goose.Lower.Validation.DeadFrontier
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyEffects

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.callExpression {module : GIR.Module} {callees : Array State} {func callee : Func}
    {moduleTypes : Array (Array (Option VTy))} {types calleeTypes : Array (Option VTy)}
    {state effects : State} {completed before : LS} {env : LEnv} {calleeProvenance : Prov}
    {index : FnId} {syntaxArgs : List Arg} {origin : OriginId}
    (frame : SourceReadyFrame module callees func types state completed)
    (closed : close module moduleTypes = some callees)
    (calleeRow : module.funcs[index]? = some callee) (effectRow : callees[index]? = some effects)
    (canonical : effects.CanonicalWithin callee calleeTypes calleeProvenance)
    (parameters : ∀ parameter root, root ∈ callee.parameterRoots parameter →
      root = .param parameter ∨ ∃ global, root = .global global)
    (bounded : LiveBound before)
    (arguments : ValuesReadyAt state (lowerArgs syntaxArgs) env before)
    (extension : (lowerExpr (.call index syntaxArgs origin) env before).2.Ext completed)
    (allocated : (lowerExpr (.call index syntaxArgs origin) env before).2.vals.size ≤ completed.vals.size)
    (resultType :
      let lowered := lowerArgs syntaxArgs env before
      let called := Lower.emitDef (.call index lowered.1 (some origin)) env lowered.2
      lowered.2.cur.isSome = true →
      (callee.results = [] ∧ types[called.1]? = some (some (.data .unit))) ∨
        ∃ type, callee.results = [type] ∧ types[called.1]? = some (some (.data type)))
    (contents :
      let lowered := lowerArgs syntaxArgs env before
      lowered.2.cur.isSome = true → ∀ position argument,
        (callee.roots.contents.find? (·.1 == position)).isSome = true →
        lowered.1[position]? = some argument → content func state (flowAt state.values argument) ≠ .pending) :
    ValueReadyAt state (lowerExpr (.call index syntaxArgs origin)) env before := by
  let lowered := lowerArgs syntaxArgs env before
  let called := Lower.emitDef (.call index lowered.1 (some origin)) env lowered.2
  let final := if env.mod.noReturn index then (emitTerm .unreachable env called.2).2 else called.2
  have run : lowerExpr (.call index syntaxArgs origin) env before = (called.1, final) := by
    cases noReturn : env.mod.noReturn index <;>
      simp [lowerExpr, bind_run, read, noReturn, lowered, called, final, pure_run]
  have afterExtension : final.Ext completed := by rw [← show (lowerExpr (.call index syntaxArgs origin) env before).2 = final from congrArg Prod.snd run]; exact extension
  have afterAllocated : final.vals.size ≤ completed.vals.size := by rw [← show (lowerExpr (.call index syntaxArgs origin) env before).2 = final from congrArg Prod.snd run]; exact allocated
  have tail : EmitsOnly (ReadyOperands state) called.2 final := by
    dsimp only [final]
    split
    · exact ready_emitTerm rfl (by intro _ value member; simp [Inst.uses, Term.uses] at member)
    · exact .refl _ _
  have calledAllocated : called.2.vals.size ≤ completed.vals.size := by
    have same : final.vals.size = called.2.vals.size := by
      dsimp only [final]
      split
      · cases current : called.2.cur with
        | none => rw [emitTerm_none _ _ current]
        | some block => rw [emitTerm_run _ _ current]
      · rfl
    rw [← same]
    exact afterAllocated
  cases current : lowered.2.cur with
  | none =>
    have calledDead : called = (0, lowered.2) := emitDef_none _ _ current
    have finalDead : final = lowered.2 := by
      dsimp only [final]
      rw [calledDead]
      split
      · exact congrArg Prod.snd (emitTerm_none _ _ current)
      · rfl
    change EmitsOnly (ReadyOperands state) before (lowerExpr (.call index syntaxArgs origin) env before).2 ∧ _
    rw [run]
    exact ⟨by simpa only [calledDead, finalDead] using arguments.1, by simp [finalDead, current]⟩
  | some block =>
    have active : lowered.2.cur.isSome = true := by simp [current]
    have calledReady := frame.callDef closed calleeRow effectRow canonical parameters
      (show Lower.emitDef (.call index lowered.1 (some origin)) env lowered.2 = called from rfl)
      (tail.extension.trans afterExtension) calledAllocated
      (liveBound_of_adv (advB_lowerArgs syntaxArgs env before _ _ rfl) bounded)
      (resultType active)
      (fun live position value row => arguments.2 live value (List.mem_of_getElem? row)) contents
    change EmitsOnly (ReadyOperands state) before (lowerExpr (.call index syntaxArgs origin) env before).2 ∧ _
    rw [run]
    refine ⟨arguments.1.trans (calledReady.1.trans tail), ?_⟩
    intro live
    apply calledReady.2
    dsimp only [final] at live
    split at live
    · exact (dead_emitTerm .unreachable).live_before rfl live
    · exact live

#print axioms SourceReadyFrame.callExpression

end Goose.Lower.Validation.ReplacementContentFlowSource
