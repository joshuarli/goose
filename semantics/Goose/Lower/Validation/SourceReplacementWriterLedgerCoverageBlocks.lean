import Goose.Lower.Validation.SourceReplacementWriterLedgerCoverageActions

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

theorem ChildrenCovered.member {property : Inst → Prop} {fragment child : Fragment}
    {env : LEnv} {before start : LS}
    (covered : ChildrenCovered property fragment env before)
    (member : some (child,start) ∈ fragment.children env before) :
    EmitsOnly property start (child.finish env start) := by
  obtain ⟨index,row⟩ := List.mem_iff_getElem?.mp member
  exact covered index child start (by simp only [Fragment.child?,row,Option.join_some])

theorem initialization_emission_coverage {property : Inst → Prop} {env : LEnv}
    {before : LS} {bindings : List (SlotId × ValueId × OriginId)}
    (events : ∀ emission ∈ initializationEmissions env bindings before, property emission.instruction) :
    At property env before (initSlots bindings) := by
  induction bindings generalizing before with
  | nil => exact .pure _ _ _ _
  | cons binding rest ih =>
    rcases binding with ⟨slot,value,origin⟩
    simp only [initSlots]
    apply At.bind
    · apply At.emitEffect
      intro live
      apply events ⟨before,(emitEffect (.slotInit slot value (some origin)) env before).2,.eff (.slotInit slot value (some origin))⟩
      exact List.mem_append_left _ (by simp [effectEmission,live])
    · apply ih
      intro emission member
      exact events emission (List.mem_append_right _ member)

theorem statementList_emission_coverage {property : Inst → Prop} {env : LEnv}
    {before : LS} {loop : Option LoopCtx} {statements : List Stmt}
    (children : ∀ child start, some (child,start) ∈ statementChildren env loop statements before →
      EmitsOnly property start (child.finish env start)) :
    At property env before (lowerStmts loop statements) := by
  induction statements generalizing before with
  | nil => exact .pure _ _ _ _
  | cons statement rest ih =>
    cases current : before.cur with
    | none =>
      have stopped : (lowerStmts loop (statement :: rest) env before).2 = before := by
        simp [lowerStmts,isLive,curBlock,bind,pure,current]
      exact .of_blocks (congrArg LS.blocks stopped)
    | some block =>
      have head : At property env before (lowerStmt loop statement) :=
        children (.statement loop statement) before (by simp [statementChildren,current])
      have tail : At property env (lowerStmt loop statement env before).2 (lowerStmts loop rest) := by
        apply ih
        intro child start member
        exact children child start (by simp only [statementChildren,current,Option.isSome_some,reduceIte]; exact List.mem_cons_of_mem _ member)
      simpa only [At,lowerStmts,bind_run,isLive_run current,reduceIte] using head.trans tail

theorem block_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (block : Core.Block) : EmissionCoverage property (.block loop bindings want block) env before := by
  intro neutral children events
  cases block with
  | mk scope statements value =>
    change At property env before (lowerBlock loop bindings want (.mk scope statements value))
    simp only [lowerBlock,inScope]
    apply At.bind (At.neutralEffect neutral (by simp [NeutralInstruction,WriterInstruction]))
    apply At.bind (At.of_blocks rfl)
    apply At.bind
    · apply At.bind
      · exact initialization_emission_coverage events
      · apply At.bind
        · apply statementList_emission_coverage
          intro child start member
          apply children.member
          exact List.mem_append_left _ member
        · apply At.bind
          · cases value with
            | none =>
              cases want
              · exact .pure _ _ _ _
              · exact At.neutralDef neutral (by intro; simp [NeutralInstruction,WriterInstruction])
            | some expression =>
              apply children.member (child := .expression expression)
              exact List.mem_append_right _ (by simp)
          · apply At.bind (At.neutralEffect neutral (by simp [NeutralInstruction,WriterInstruction]))
            exact At.pure _ _ _ _
    · apply At.bind (At.of_blocks rfl)
      exact At.pure _ _ _ _

#print axioms statementList_emission_coverage
#print axioms block_emission_coverage

end Goose.Lower.Validation.SourceReplacementWriterLedger
