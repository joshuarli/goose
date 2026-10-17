import Goose.Lower.Validation.SummaryPreservationReturnLedgerControlOptional

namespace Goose.Lower.Validation.SummaryPreservation.ReturnLedgerControl

open Goose.Core Goose.GIR ReturnFrames

def ifSetup (condition : Expr) : B (Option BlockId) := do
  let value ← lowerExpr condition
  whenLive none fun _ => do
    let (yes, other) ← fork value
    setCur (some yes)
    pure (some other)

def ifElseSetup (loop : Option LoopCtx) (condition : Expr) (yes : Core.Block) : B (Option (Option BlockId)) := do
  let selected ← ifSetup condition
  match selected with
  | none => pure none
  | some other =>
    let _ ← lowerBlock loop [] false yes
    let ending ← curBlock
    setCur (some other)
    pure (some ending)

private theorem absent_ifSetup {avoid : List ValueId × Option OriginId} {condition : Expr}
    (free : ReturnFreeExpr condition) : ReturnAbsentRun (avoid := avoid) (ifSetup condition) := by
  unfold ifSetup
  refine ReturnAbsentRun.bind (returnAbsent_lowerExpr condition free) fun value => ?_
  apply returnAbsent_whenLive
  intro _
  refine ReturnAbsentRun.bind (returnAbsent_fork value) fun _ => ?_
  exact ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => returnAbsent_pure _

theorem ifNone_factor (loop : Option LoopCtx) (condition : Expr) (yes : Core.Block) (origin : OriginId) :
    lowerStmt loop (.ifS condition yes none origin) = (do
      let selected ← ifSetup condition
      match selected with
      | none => pure ()
      | some other =>
        let _ ← lowerBlock loop [] false yes
        emitTerm (.br other [])
        setCur (some other)) := by
  funext env state
  simp only [lowerStmt, ifSetup, bind_run]
  cases current : (lowerExpr condition env state).2.cur
  · simp only [whenLive_none _ _ _ current, pure_run]
  · simp only [whenLive_some _ _ _ current, bind_run, pure_run]

theorem ifSome_factor (loop : Option LoopCtx) (condition : Expr) (yes no : Core.Block) (origin : OriginId) :
    lowerStmt loop (.ifS condition yes (some no) origin) = (do
      let selected ← ifElseSetup loop condition yes
      match selected with
      | none => pure ()
      | some ending =>
        let _ ← lowerBlock loop [] false no
        let last ← curBlock
        joinArms ending last) := by
  funext env state
  simp only [lowerStmt, ifElseSetup, ifSetup, bind_run]
  cases current : (lowerExpr condition env state).2.cur
  · simp only [whenLive_none _ _ _ current, pure_run]
  · simp only [whenLive_some _ _ _ current, bind_run, pure_run]

theorem ifNone_origin {sourceEnv : TEnv} {condition : Expr} {yes : Core.Block} {sourceOrigin : OriginId}
    {type : Ty} {start finish : Nat} {env : LEnv} {initial final : LS} {result : Unit}
    {values : List ValueId} {origin : Option OriginId} (loop : Option LoopCtx)
    (source : Core.tyExpr sourceEnv condition start = .ok (type, finish))
    (run : lowerStmt loop (.ifS condition yes none sourceOrigin) env initial = (result, final))
    (member : .term (.ret values origin) ∈ final.insts) :
    .term (.ret values origin) ∈ initial.insts ∨ Nonempty (ActiveReturnCheckpoint (ifSetup condition)
      (fun _ => lowerBlock loop [] false yes) env initial values origin) := by
  rw [ifNone_factor] at run
  exact optional_origin (setup := ifSetup condition) (env := env) (initial := initial) (final := final) (result := result)
    (child := fun _ => lowerBlock loop [] false yes)
    (suffix := fun other (_ : ValueId) => do emitTerm (.br other []); setCur (some other))
    (frame _ (fun _ => absent_ifSetup (tyExpr_returnFree condition source)))
    (fun _ _ => frame_bind (frame _ (fun _ => returnAbsent_emitTerm _ (by intro _ _ same; cases same)))
      (fun _ => frame _ (fun _ => returnAbsent_setCur _))) (by
      simp only [bind_run] at run ⊢
      generalize selection : ifSetup condition env initial = pair at run ⊢
      obtain ⟨selected, state⟩ := pair
      cases selected <;> exact run) member

theorem ifSome_origin {sourceEnv : TEnv} {condition : Expr} {yes no : Core.Block} {sourceOrigin : OriginId}
    {type : Ty} {start finish : Nat} {env : LEnv} {initial final : LS} {result : Unit}
    {values : List ValueId} {origin : Option OriginId} (loop : Option LoopCtx)
    (source : Core.tyExpr sourceEnv condition start = .ok (type, finish))
    (run : lowerStmt loop (.ifS condition yes (some no) sourceOrigin) env initial = (result, final))
    (member : .term (.ret values origin) ∈ final.insts) :
    .term (.ret values origin) ∈ initial.insts ∨ Nonempty (ActiveReturnCheckpoint (ifElseSetup loop condition yes)
      (fun _ => lowerBlock loop [] false no) env initial values origin) := by
  rw [ifSome_factor] at run
  exact optional_origin_none (setup := ifElseSetup loop condition yes) (env := env) (initial := initial) (final := final) (result := result)
    (child := fun _ => lowerBlock loop [] false no)
    (suffix := fun ending (_ : ValueId) => do let last ← curBlock; joinArms ending last)
    (by
      intro before setupRun
      change (ifSetup condition >>= _) env initial = (none, before) at setupRun
      obtain ⟨selected, selectedState, selecting, tail⟩ := bind_eq.mp setupRun
      cases selected with
      | none =>
        have stateEq := (pure_eq.mp tail).2
        subst before
        exact (frame _ (fun _ => absent_ifSetup (tyExpr_returnFree condition source))) env initial none selectedState selecting
      | some other =>
        simp only [bind_eq, pure_eq] at tail
        obtain ⟨_, _, _, _, _, _, _, _, _, impossible, _⟩ := tail
        cases impossible)
    (fun _ _ => frame _ (fun _ => ReturnAbsentRun.bind returnAbsent_curBlock fun ending => returnAbsent_joinArms _ ending))
    (by
      simp only [bind_run] at run ⊢
      generalize selection : ifElseSetup loop condition yes env initial = pair at run ⊢
      obtain ⟨selected, state⟩ := pair
      cases selected <;> exact run) member

end Goose.Lower.Validation.SummaryPreservation.ReturnLedgerControl
