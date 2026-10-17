import Goose.Lower.Validation.SourceReplacementWriterLedgerCoverageLoops

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

theorem neutral_regrowOf (owner : Option ValueId) : EmitsOnlyRun NeutralInstruction (regrowOf owner) := by
  apply EmitsOnlyRun.unchanged
  intro env before
  cases owner with
  | none => rfl
  | some owner =>
    simp only [regrowOf,growOwner,bind_run,valTy_run]
    cases (valTy owner env before).1 with
    | data type => cases type <;> rfl
    | view _ _ => rfl

theorem neutral_eachSampled (regrow : Bool) (view : ValueId) :
    EmitsOnlyRun NeutralInstruction (eachSampled regrow view) := by
  cases regrow with
  | false => exact neutral_emitDef _ (by intro; simp [NeutralInstruction,WriterInstruction])
  | true => exact .pure _ _

theorem neutral_eachLen (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    EmitsOnlyRun NeutralInstruction (eachLen regrow owner sampled) := by
  cases regrow with
  | false => exact .pure _ _
  | true => exact neutral_emitDef _ (by intro; simp [NeutralInstruction,WriterInstruction])

theorem neutral_eachElemValue (variableId : VarId) (byRef : Bool) (element : ValueId) :
    EmitsOnlyRun NeutralInstruction (eachElemValue variableId byRef element) := by
  cases byRef with
  | false => exact neutral_emitDef _ (by intro; simp [NeutralInstruction,WriterInstruction])
  | true =>
    unfold eachElemValue
    simp only [reduceIte]
    apply EmitsOnlyRun.bind (EmitsOnlyRun.unchanged (fun _ _ => rfl))
    intro env
    cases found : env.vars[variableId]? with
    | none => exact .pure _ _
    | some localVar =>
      simp only
      cases type : localVar.ty <;> simp only [type] <;>
        first | exact .pure _ _ | exact neutral_borrowTo _ _

theorem each_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (variableId : VarId) (index : Option VarId) (view : View)
    (byRef : Bool) (body : Core.Block) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.forEach variableId index view byRef body origin)) env before := by
  intro neutral children events
  change At property env before (lowerStmt loop (.forEach variableId index view byRef body origin))
  simp only [lowerStmt,lowerEach,loopBody]
  apply At.bind
  · have viewed := children 0 (.view view) before rfl
    cases view <;> exact viewed
  · apply At.bind (At.neutral neutral (neutral_regrowOf _))
    apply At.bind (At.neutral neutral (neutral_eachSampled _ _))
    apply At.bind (At.neutralDef neutral (by intro; simp [NeutralInstruction,WriterInstruction]))
    apply At.whenLive
    intro block current
    apply At.bind (At.of_run (emitsOnly_newBlock _ _))
    apply At.bind (At.term _ neutral)
    apply At.bind (At.of_run (emitsOnly_setCur _ _))
    apply At.bind (At.neutral neutral (neutral_eachLen _ _ _))
    apply At.bind (At.neutralDef neutral (by intro; simp [NeutralInstruction,WriterInstruction]))
    apply At.bind (At.of_blocks rfl)
    apply At.bind (At.of_run (emitsOnly_fork property (fun term => neutral _ (by simp [WriterInstruction])) _))
    apply At.bind (At.of_run (emitsOnly_setCur _ _))
    apply At.bind
    · apply At.bind (At.neutralDef neutral (by intro; simp [NeutralInstruction,WriterInstruction]))
      apply At.bind (At.neutral neutral (neutral_eachElemValue _ _ _))
      apply children 1 (.block _ _ false body) _
      simp [Fragment.child?,Fragment.children,eachChild,current,get_apply]
      cases index <;> rfl
    · apply At.bind (At.neutral neutral (neutral_rangeBack _ _ _))
      exact At.of_run (emitsOnly_setCur _ _)

#print axioms each_emission_coverage

end Goose.Lower.Validation.SourceReplacementWriterLedger
