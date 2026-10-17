import Goose.Lower.Validation.EmittedTypingBuilder

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem EmittedRun.whenLive (default : α) (body : BlockId → B α)
    (bodyTrace : ∀ block, EmittedRun (body block)) : EmittedRun (Goose.Lower.whenLive default body) := by
  unfold Goose.Lower.whenLive
  apply EmittedRun.curBlock.bind
  intro current
  cases current with
  | none => exact EmittedRun.pure _
  | some block => exact bodyTrace block

theorem EmittedRun.leaveAll : ∀ scopes, EmittedRun (Goose.Lower.leaveAll scopes)
  | [] => EmittedRun.pure _
  | scope :: rest => (EmittedRun.emitEffect (.leave scope)).bind fun _ => EmittedRun.leaveAll rest

theorem EmittedRun.leaveTo (depth : Nat) : EmittedRun (Goose.Lower.leaveTo depth) := by
  unfold Goose.Lower.leaveTo
  exact EmittedRun.get.bind fun state => EmittedRun.leaveAll _

theorem EmittedRun.inScope (scope : ScopeId) {body : B α} (bodyTrace : EmittedRun body) :
    EmittedRun (Goose.Lower.inScope scope body) := by
  unfold Goose.Lower.inScope
  exact (EmittedRun.pushScope scope).bind fun _ => bodyTrace.bind fun value =>
    EmittedRun.popScope.bind fun _ => EmittedRun.pure value

theorem EmittedRun.initSlots : ∀ slots, EmittedRun (Goose.Lower.initSlots slots)
  | [] => EmittedRun.pure _
  | (_, _, _) :: rest => (EmittedRun.emitEffect _).bind fun _ => EmittedRun.initSlots rest

theorem EmittedRun.fork (condition : ValueId) : EmittedRun (Goose.Lower.fork condition) := by
  unfold Goose.Lower.fork
  exact (EmittedRun.newBlock []).bind fun _ => (EmittedRun.newBlock []).bind fun _ =>
    (EmittedRun.emitTerm _).bind fun _ => EmittedRun.pure _

theorem EmittedRun.scFork (isAnd : Bool) (condition : ValueId) :
    EmittedRun (Goose.Lower.scFork isAnd condition) := by
  cases isAnd <;> unfold Goose.Lower.scFork
  all_goals exact (EmittedRun.newBlock []).bind fun _ => (EmittedRun.newBlock [.data .bool]).bind fun _ =>
    (EmittedRun.emitTerm _).bind fun _ => EmittedRun.pure _

theorem EmittedRun.shortCircuit (isAnd : Bool) (condition : ValueId) {rhs : B ValueId}
    (rhsTrace : EmittedRun rhs) : EmittedRun (Goose.Lower.shortCircuit isAnd condition rhs) := by
  unfold Goose.Lower.shortCircuit
  apply EmittedRun.whenLive
  intro current
  exact (EmittedRun.scFork isAnd condition).bind fun _ =>
    (EmittedRun.setCur _).bind fun _ => rhsTrace.bind fun _ =>
    (EmittedRun.emitTerm _).bind fun _ => (EmittedRun.setCur _).bind fun _ => EmittedRun.pure _

theorem EmittedRun.patchBrs (join : BlockId) : ∀ incoming, EmittedRun (Goose.Lower.patchBrs join incoming)
  | [] => EmittedRun.pure _
  | (_, _) :: rest => (EmittedRun.patchTerm _ _).bind fun _ => EmittedRun.patchBrs join rest

theorem EmittedRun.patchBrs0 (join : BlockId) : ∀ incoming, EmittedRun (Goose.Lower.patchBrs0 join incoming)
  | [] => EmittedRun.pure _
  | _ :: rest => (EmittedRun.patchTerm _ _).bind fun _ => EmittedRun.patchBrs0 join rest

theorem EmittedRun.joinValue (ends : Option BlockId × Option BlockId) (left right : ValueId) :
    EmittedRun (Goose.Lower.joinValue ends.1 left ends.2 right) := by
  rcases ends with ⟨leftEnd, rightEnd⟩
  cases leftEnd <;> cases rightEnd <;> unfold Goose.Lower.joinValue
  all_goals first
    | exact (EmittedRun.setCur _).bind fun _ => EmittedRun.pure _
    | exact EmittedRun.pure _
    | exact (EmittedRun.valTy _).bind fun _ => (EmittedRun.newBlock _).bind fun _ =>
        (EmittedRun.patchBrs _ _).bind fun _ => (EmittedRun.setCur _).bind fun _ => EmittedRun.pure _

theorem EmittedRun.joinArms (left right : Option BlockId) :
    EmittedRun (Goose.Lower.joinArms left right) := by
  cases left <;> cases right <;> unfold Goose.Lower.joinArms
  all_goals first
    | exact EmittedRun.setCur _
    | exact (EmittedRun.newBlock []).bind fun _ => (EmittedRun.patchBrs0 _ _).bind fun _ => EmittedRun.setCur _

end Goose.Lower.Validation
