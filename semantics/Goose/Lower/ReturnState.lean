import Goose.Lower.Unwind
import Goose.Lower.RuntimeSim

namespace Goose.Lower

open Goose.Core Goose.GIR

def prepareReturn (env : Env) : Flow → M Flow
  | .ret value => do
    releaseScopes env env.scopes
    pure (.ret value)
  | flow => pure flow

theorem prepareReturn_no_scopes (env : Env) (hscopes : env.scopes = []) :
    prepareReturn env = fun flow => pure flow := by
  funext flow
  cases flow <;> simp [prepareReturn, hscopes, releaseScopes, pure_bind]

structure ReturnSite (cx : FnCtx) (pt : Pt) (frame : GIR.Frame) (value : Val)
    (org : OriginId) : Prop where
  instruction : ∃ ids, instAt cx.fn pt = some (.term (.ret ids (some org))) ∧
    ((ids = [] ∧ value = .unit) ∨ ∃ id, ids = [id] ∧ frame.vals[id]? = some (.val value))
  scopes : frame.scopes = []

theorem ReturnSite.run {cx : FnCtx} {pt : Pt} {frame : GIR.Frame} {value : Val} {org : OriginId}
    (h : ReturnSite cx pt frame value org) (state : St) :
    ∀ extra, runAt cx pt frame (extra + 1) state = .ok value state := by
  intro extra
  obtain ⟨ids, hinst, hvalue⟩ := h.instruction
  rcases hvalue with ⟨rfl, rfl⟩ | ⟨id, rfl, hcell⟩
  · rw [runAt_ret0 hinst extra]
    rfl
  · rw [runAt_ret1 hinst hcell extra]
    rfl


end Goose.Lower
