import Goose.Lower.Validation.DeadFrontier

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure ReplacementEmissionSite (env : LEnv) (initial finished : LS)
    (place : Place) (rhs : Expr) (origin : OriginId) where
  owner : ValueId
  value : ValueId
  addressed : LS
  cleared : LS
  captured : LS
  addressRun : lowerPlace place env initial = (owner, addressed)
  clearRun : emitEffect (.clear owner (some origin)) env addressed = ((), cleared)
  rhsRun : lowerExpr rhs env cleared = (value, captured)
  publishRun : emitEffect (.replace owner value (some origin)) env captured = ((), finished)

theorem replacementEmissionSite_of_run {env : LEnv} {initial finished : LS}
    {place : Place} {rhs : Expr} {origin : OriginId} {loop : Option LoopCtx}
    (run : lowerStmt loop (.assignWhole place rhs origin) env initial = ((), finished)) :
    Nonempty (ReplacementEmissionSite env initial finished place rhs origin) := by
  obtain ⟨owner, addressed, addressRun, rest⟩ := bind_eq.mp run
  obtain ⟨unit, cleared, clearRun, rest⟩ := bind_eq.mp rest
  cases unit
  obtain ⟨value, captured, rhsRun, publishRun⟩ := bind_eq.mp rest
  exact ⟨⟨owner, value, addressed, cleared, captured, addressRun, clearRun, rhsRun, publishRun⟩⟩

theorem emitEffect_current {env : LEnv} {before after : LS} {effect : Effect} {value : Unit}
    (run : emitEffect effect env before = (value, after)) : after.cur = before.cur := by
  cases current : before.cur with
  | none => rw [emitEffect_none _ _ current] at run; cases run; exact current
  | some index => rw [emitEffect_run _ _ current] at run; cases run; exact current

theorem ReplacementEmissionSite.current {env : LEnv} {initial finished : LS}
    {place : Place} {rhs : Expr} {origin : OriginId}
    (site : ReplacementEmissionSite env initial finished place rhs origin) :
    site.captured.cur = finished.cur :=
  (emitEffect_current site.publishRun).symm

theorem ReplacementEmissionSite.addressed_live {env : LEnv} {initial finished : LS}
    {place : Place} {rhs : Expr} {origin : OriginId}
    (site : ReplacementEmissionSite env initial finished place rhs origin)
    (live : finished.cur.isSome = true) : site.addressed.cur.isSome = true := by
  have capturedLive : site.captured.cur.isSome = true := by rw [site.current]; exact live
  have clearedLive := (dead_lowerExpr rhs).live_before site.rhsRun capturedLive
  exact (dead_emitEffect (.clear site.owner (some origin))).live_before site.clearRun clearedLive

end Goose.Lower.Validation
