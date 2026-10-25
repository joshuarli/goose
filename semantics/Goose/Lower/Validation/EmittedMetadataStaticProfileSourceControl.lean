import Goose.Lower.Validation.EmittedMetadataStaticProfileSourceBuilder

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

variable {profile : ArtifactProfile} {le : LEnv}

theorem EmittedProfileRun.whenLive (default : α) (body : BlockId → B α)
    (bodyTrace : ∀ block, EmittedProfileRun profile le (body block)) : EmittedProfileRun profile le (Goose.Lower.whenLive default body) := by
  unfold Goose.Lower.whenLive
  apply EmittedProfileRun.curBlock.bind
  intro current
  cases current with
  | none => exact EmittedProfileRun.pure _
  | some block => exact bodyTrace block

theorem EmittedProfileRun.leaveAll : ∀ scopes, EmittedProfileRun profile le (Goose.Lower.leaveAll scopes)
  | [] => EmittedProfileRun.pure _
  | scope :: rest => (EmittedProfileRun.emitEffect (.leave scope) trivial).bind fun _ => EmittedProfileRun.leaveAll rest

theorem EmittedProfileRun.leaveTo (depth : Nat) : EmittedProfileRun profile le (Goose.Lower.leaveTo depth) := by
  unfold Goose.Lower.leaveTo
  exact EmittedProfileRun.get.bind fun state => EmittedProfileRun.leaveAll _

theorem EmittedProfileRun.inScope (scope : ScopeId) {body : B α} (bodyTrace : EmittedProfileRun profile le body) :
    EmittedProfileRun profile le (Goose.Lower.inScope scope body) := by
  unfold Goose.Lower.inScope
  exact (EmittedProfileRun.pushScope scope).bind fun _ => bodyTrace.bind fun value =>
    EmittedProfileRun.popScope.bind fun _ => EmittedProfileRun.pure value

theorem EmittedProfileRun.initSlots : ∀ slots, EmittedProfileRun profile le (Goose.Lower.initSlots slots)
  | [] => EmittedProfileRun.pure _
  | (slot, value, origin) :: rest => (EmittedProfileRun.emitEffect (.slotInit slot value (some origin)) trivial).bind fun _ => EmittedProfileRun.initSlots rest

theorem EmittedProfileRun.fork (condition : ValueId) : EmittedProfileRun profile le (Goose.Lower.fork condition) := by
  unfold Goose.Lower.fork
  exact (EmittedProfileRun.newBlock []).bind fun yes => (EmittedProfileRun.newBlock []).bind fun no =>
    (EmittedProfileRun.emitTerm (.condbr condition yes.1 [] no.1 []) trivial).bind fun _ => EmittedProfileRun.pure (yes.1, no.1)

theorem EmittedProfileRun.scFork (isAnd : Bool) (condition : ValueId) :
    EmittedProfileRun profile le (Goose.Lower.scFork isAnd condition) := by
  cases isAnd <;> unfold Goose.Lower.scFork
  · exact (EmittedProfileRun.newBlock []).bind fun rhs => (EmittedProfileRun.newBlock [.data .bool]).bind fun join =>
      (EmittedProfileRun.emitTerm (.condbr condition join.1 [condition] rhs.1 []) trivial).bind fun _ => EmittedProfileRun.pure _
  · exact (EmittedProfileRun.newBlock []).bind fun rhs => (EmittedProfileRun.newBlock [.data .bool]).bind fun join =>
      (EmittedProfileRun.emitTerm (.condbr condition rhs.1 [] join.1 [condition]) trivial).bind fun _ => EmittedProfileRun.pure _

theorem EmittedProfileRun.shortCircuit (isAnd : Bool) (condition : ValueId) {rhs : B ValueId}
    (rhsTrace : EmittedProfileRun profile le rhs) : EmittedProfileRun profile le (Goose.Lower.shortCircuit isAnd condition rhs) := by
  unfold Goose.Lower.shortCircuit
  apply EmittedProfileRun.whenLive
  intro current
  exact (EmittedProfileRun.scFork isAnd condition).bind fun parts =>
    (EmittedProfileRun.setCur _).bind fun _ => rhsTrace.bind fun value =>
    (EmittedProfileRun.emitTerm (.br parts.2.1 [value]) trivial).bind fun _ => (EmittedProfileRun.setCur _).bind fun _ => EmittedProfileRun.pure _

theorem EmittedProfileRun.patchBrs (join : BlockId) : ∀ incoming, EmittedProfileRun profile le (Goose.Lower.patchBrs join incoming)
  | [] => EmittedProfileRun.pure _
  | (block, value) :: rest => (EmittedProfileRun.patchTerm block (.br join [value]) trivial).bind fun _ => EmittedProfileRun.patchBrs join rest

theorem EmittedProfileRun.patchBrs0 (join : BlockId) : ∀ incoming, EmittedProfileRun profile le (Goose.Lower.patchBrs0 join incoming)
  | [] => EmittedProfileRun.pure _
  | block :: rest => (EmittedProfileRun.patchTerm block (.br join []) trivial).bind fun _ => EmittedProfileRun.patchBrs0 join rest

theorem EmittedProfileRun.joinValue (ends : Option BlockId × Option BlockId) (left right : ValueId) :
    EmittedProfileRun profile le (Goose.Lower.joinValue ends.1 left ends.2 right) := by
  rcases ends with ⟨leftEnd, rightEnd⟩
  cases leftEnd <;> cases rightEnd <;> unfold Goose.Lower.joinValue
  all_goals first
    | exact (EmittedProfileRun.setCur _).bind fun _ => EmittedProfileRun.pure _
    | exact EmittedProfileRun.pure _
    | exact (EmittedProfileRun.valTy _).bind fun _ => (EmittedProfileRun.newBlock _).bind fun _ =>
        (EmittedProfileRun.patchBrs _ _).bind fun _ => (EmittedProfileRun.setCur _).bind fun _ => EmittedProfileRun.pure _

theorem EmittedProfileRun.joinArms (left right : Option BlockId) :
    EmittedProfileRun profile le (Goose.Lower.joinArms left right) := by
  cases left <;> cases right <;> unfold Goose.Lower.joinArms
  all_goals first
    | exact EmittedProfileRun.setCur _
    | exact (EmittedProfileRun.newBlock []).bind fun _ => (EmittedProfileRun.patchBrs0 _ _).bind fun _ => EmittedProfileRun.setCur _

end Goose.Lower.Validation
