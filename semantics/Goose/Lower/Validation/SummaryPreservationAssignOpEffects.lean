import Goose.Lower.Validation.SummaryPreservationAssignOpSource

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem assignOp_instruction_effects {env : PEnv} {context : ContextId}
    {op : BinOp} {place : Place} {expression : Expr} {org : OriginId}
    {initial placeState before after : RState} {placeRoots valueRoots : List RootRef}
    {vt : Array (Option VTy)} {loadRoots storeRoots : Prov}
    {address old rhs result : ValueId} {ty : IntTy} {target : Core.Eff}
    (accepted : Core.validate env.mod = .ok ())
    (contextLookup : env.mod.contexts[context]? = some env.ctx)
    (implLookup : env.mod.impls[env.ctx.impl]? = some env.impl)
    (placeReplay : rpPlace env place initial = .ok (placeRoots, placeState))
    (valueReplay : rpExpr env expression placeState = .ok (valueRoots, before))
    (source : rpStmt env (.assignOp op place expression org) initial = .ok ((), after))
    (loadRefines : RootsRefine (lowerContextAt env.mod env.ctx env.impl)
      (rootsAt loadRoots.vals address) placeRoots)
    (storeRefines : RootsRefine (lowerContextAt env.mod env.ctx env.impl)
      (rootsAt storeRoots.vals address) placeRoots)
    (owner : (ownerTy vt address).any Ty.isRefLike = false)
    (wholeEffect : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target) :
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl)
        ((lowerContextAt env.mod env.ctx env.impl).effectStep (lower env.mod) vt loadRoots {}
          (.def old (.load address))) target ∧
      EffectRefinement (lowerContextAt env.mod env.ctx env.impl)
        ((lowerContextAt env.mod env.ctx env.impl).effectStep (lower env.mod) vt storeRoots {}
          (.def result (.bin op ty old rhs (some org)))) target ∧
      EffectRefinement (lowerContextAt env.mod env.ctx env.impl)
        ((lowerContextAt env.mod env.ctx env.impl).effectStep (lower env.mod) vt storeRoots {}
          (.eff (.store address result (some org)))) target := by
  rw [rpStmt_assignOp_after_operands placeReplay valueReplay] at source
  cases source
  have closed := lowerContextAt_parameterRoots_closed accepted contextLookup implLookup
  have loadBound := effectStep_load_refines (module := lower env.mod) (vt := vt)
    (provenance := loadRoots) (result := old) closed
    (effectRefinement_empty (lowerContextAt env.mod env.ctx env.impl) before.eff) loadRefines
  have binBound := effectStep_bin_refines (module := lower env.mod) (vt := vt)
    (provenance := storeRoots) (result := result) (left := old) (right := rhs)
    (op := op) (ty := ty) (origin := some org)
    (effectRefinement_empty (lowerContextAt env.mod env.ctx env.impl) before.eff)
  have storeBound := effectStep_store_nonref_refines (vt := vt) (provenance := storeRoots)
    (value := result) (origin := org) (source := before.eff)
    accepted contextLookup implLookup storeRefines owner
  exact ⟨(loadBound.trans effectRefinement_assignOp_reads).trans wholeEffect,
    (binBound.trans effectRefinement_assignOp_bin).trans wholeEffect,
    (storeBound.trans effectRefinement_assignOp_writes).trans wholeEffect⟩

end Goose.Lower.Validation.SummaryPreservation
