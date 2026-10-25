import Goose.Lower.Validation.SourceReplacementLexicalWritersPhysics
import Goose.Lower.Validation.SourceReplacementLexicalWritersStorePhysics

namespace Goose.Lower.Validation.SourceReplacementLexicalWriters

open Goose.Core Goose.GIR ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem emitted_binary_nonref (facts : SourceReadyFunction)
    {env : LEnv} {before after : LS} {left right value : ValueId}
    {operation : BinOp} {integer : IntTy} {origin : Option OriginId}
    (bounded : LiveBound before)
    (run : emitDef (.bin operation integer left right origin) env before = (value,after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation facts.func after) :
    valRefLike facts.types value = false := by
  obtain ⟨block, member, definition⟩ := emitted_definition_liveBound bounded run live continuation
  have typed := facts.native.typing block member _ definition
  cases typed with
  | definition _ _ type checked canonical =>
    have shape : type = .data (.int integer) := by
      cases leftAt : ({(lower facts.source.mod).tyEnv facts.func with vals := facts.types} : TyEnv).intTy left with
      | error message => simp [Op.resultTy, leftAt, bind, Except.bind] at checked
      | ok leftType =>
        cases rightAt : ({(lower facts.source.mod).tyEnv facts.func with vals := facts.types} : TyEnv).intTy right with
        | error message => simp [Op.resultTy, leftAt, rightAt, bind, Except.bind] at checked
        | ok rightType =>
          simp only [Op.resultTy, leftAt, rightAt, bind, Except.bind] at checked
          split at checked
          · simpa [pure, Except.pure] using checked.symm
          · simp [Goose.GIR.tyErr, bind, Except.bind] at checked
    subst type
    simp [valRefLike, canonical, VTy.refLike, Ty.isRefLike]

theorem integer_type_state (value : ValueId) (env : LEnv) (state : LS) :
    ∃ integer, intTyOf value env state = (integer,state) := by
  simp only [intTyOf, bind_run]
  generalize row : valTy value env state = pair
  have same : pair.2 = state := row ▸ valTy_run value env state
  obtain ⟨type, next⟩ := pair
  cases type <;> simp_all [pure_run]
  case data type => cases type <;> simp_all [pure_run]

#print axioms emitted_binary_nonref
#print axioms integer_type_state

end Goose.Lower.Validation.SourceReplacementLexicalWriters
