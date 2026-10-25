import Goose.Lower.Validation.SourceReadyObservationLoopsStatements
import Goose.Lower.Validation.SourceReadyObservationAccess

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {func : Func} {state : State} {le : LEnv} {before : LS}

theorem observation_regrow (owner : Option ValueId) :
    EmitsOnlyRun (ReadyCallObservations module func state) (regrowOf owner) := by
  cases owner with
  | none => exact .pure _ _
  | some address =>
    unfold regrowOf growOwner
    apply (ReadyCallObservations.valueType address).bind
    intro type
    cases type with
    | data type => cases type <;> exact .pure _ _
    | view => exact .pure _ _

theorem observation_eachSampled (regrow : Bool) (view : ValueId) :
    EmitsOnlyRun (ReadyCallObservations module func state) (eachSampled regrow view) := by
  cases regrow with
  | true => exact .pure _ _
  | false => exact ReadyCallObservations.emitDefinition _ (by intros; intro same; cases same)

theorem observation_eachElement (variableId : VarId) (byRef : Bool) (address : ValueId) :
    EmitsOnlyRun (ReadyCallObservations module func state) (eachElemValue variableId byRef address) := by
  unfold eachElemValue
  cases byRef with
  | false => exact ReadyCallObservations.emitDefinition _ (by intros; intro same; cases same)
  | true =>
    apply EmitsOnlyRun.bind (EmitsOnlyRun.unchanged (by intros; rfl))
    intro env
    cases row : env.vars[variableId]? with
    | none => exact .pure _ _
    | some localVar =>
      simp only
      cases type : localVar.ty <;> simp only [type] <;> first | exact .pure _ _ | exact ReadyCallObservations.borrow _ _

theorem observation_eachStatement (loop : Option LoopCtx) (variableId : VarId) (index : Option VarId)
    (view : Core.View) (byRef : Bool) (body : Core.Block) (origin : OriginId) :
    let source := lowerEachSource view le before
    let regrow := regrowOf source.1.1 le source.2
    let sampled := eachSampled regrow.1 source.1.2 le regrow.2
    let start := emitDef (.constInt .i64 0) le sampled.2
    let allocated := newBlock [.data (.int .i64)] le start.2
    let counter := allocated.1.2.headD 0
    let bridged := (emitTerm (.br allocated.1.1 [start.1]) le allocated.2).2
    let header := (setCur (some allocated.1.1) le bridged).2
    let length := eachLen regrow.1 source.1.1 sampled.1 le header
    let compared := emitDef (.cmp .lt .i64 counter length.1) le length.2
    let split := fork compared.1 le compared.2
    let input := (setCur (some split.1.1) le split.2).2
    let address := emitDef (.refElem source.1.2 counter) le input
    let value := eachElemValue variableId byRef address.1 le address.2
    let bindings := (variableId, value.1, origin) :: (match index with
      | some j => [(j, counter, origin)] | none => [])
    EmitsOnly (ReadyCallObservations module func state) before source.2 →
    (start.2.cur.isSome = true → EmitsOnly (ReadyCallObservations module func state) value.2
      (lowerBlock (some ⟨compared.2.stack.length, split.1.2, .next allocated.1.1 .i64 counter⟩)
        bindings false body le value.2).2) →
    EmitsOnly (ReadyCallObservations module func state) before
      (lowerStmt loop (.forEach variableId index view byRef body origin) le before).2 := by
  dsimp only
  intro sourceChild bodyChild
  unfold lowerStmt
  apply observation_bind (le := le) sourceChild
  apply observation_bind (le := le) (action := regrowOf _)
    (observation_regrow _ le _ _ _ rfl)
  apply observation_bind (le := le) (action := eachSampled _ _)
    (observation_eachSampled _ _ le _ _ _ rfl)
  apply observation_bind (le := le) (action := emitDef (.constInt .i64 0))
    (ReadyCallObservations.emitDefinition _ (by intros; intro same; cases same) le _ _ _ rfl)
  apply observation_whenLive
  intro block current
  apply observation_bind (le := le) (emitsOnly_newBlock _ _ le _ _ _ rfl)
  apply observation_bind (le := le)
  · exact observation_term _ le _ _ _ rfl
  apply observation_bind (le := le) (emitsOnly_setCur _ _ le _ _ _ rfl)
  apply observation_each
  apply observation_bind (le := le) (action := emitDef (.refElem _ _))
    (ReadyCallObservations.emitDefinition _ (by intros; intro same; cases same) le _ _ _ rfl)
  apply observation_bind (le := le) (action := eachElemValue variableId byRef _)
    (observation_eachElement variableId byRef _ le _ _ _ rfl)
  exact bodyChild (by simp [current])

#print axioms observation_regrow
#print axioms observation_eachSampled
#print axioms observation_eachElement
#print axioms observation_eachStatement

end Goose.Lower.Validation.ReplacementContentFlowSource
