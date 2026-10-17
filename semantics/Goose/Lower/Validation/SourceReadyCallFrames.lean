import Goose.Lower.Validation.ValueTypes
import Goose.Lower.Frag

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR

theorem lower_call_run (callee : ContextId) (arguments : List Arg) (origin : OriginId)
    (env : LEnv) (before : LS) :
    let lowered := lowerArgs arguments env before
    let called := Lower.emitDef (.call callee lowered.1 (some origin)) env lowered.2
    lowerExpr (.call callee arguments origin) env before =
      (called.1, if env.mod.noReturn callee then (Lower.emitTerm .unreachable env called.2).2 else called.2) := by
  dsimp only
  cases noReturn : env.mod.noReturn callee <;>
    simp [lowerExpr, bind_run, read, noReturn, pure_run]

theorem call_emission_advance (callee : ContextId) (arguments : List Arg) (origin : OriginId)
    (env : LEnv) (before : LS) :
    let lowered := lowerArgs arguments env before
    let called := Lower.emitDef (.call callee lowered.1 (some origin)) env lowered.2
    called.2.Adv (lowerExpr (.call callee arguments origin) env before).2 := by
  dsimp only
  rw [lower_call_run]
  cases noReturn : env.mod.noReturn callee with
  | false => simp only [Bool.false_eq_true, reduceIte]; exact LS.Adv.refl _
  | true => simp only [reduceIte]; exact advB_emitTerm .unreachable env _ _ _ rfl

theorem call_emission_types (callee : ContextId) (arguments : List Arg) (origin : OriginId)
    (env : LEnv) (before : LS) :
    let lowered := lowerArgs arguments env before
    let called := Lower.emitDef (.call callee lowered.1 (some origin)) env lowered.2
    TypePrefix called.2 (lowerExpr (.call callee arguments origin) env before).2 := by
  dsimp only
  rw [lower_call_run]
  cases noReturn : env.mod.noReturn callee with
  | false => simp only [Bool.false_eq_true, reduceIte]; exact TypePrefix.refl _
  | true => simp only [reduceIte]; exact types_emitTerm .unreachable env _ _ _ rfl

#print axioms lower_call_run
#print axioms call_emission_advance
#print axioms call_emission_types

end Goose.Lower.Validation.ReplacementContentFlowSource
