import Goose.Lower.Validation.SummaryPreservationRefinedBuilder

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem rootsOfDef_ownerBorrow (results : Array (List RootRef)) (vt : Array (Option VTy))
    (func : Func) (provenance : Prov) (result owner : ValueId) :
    rootsOfDef results vt func provenance result (.ownerBorrow owner) =
      rootsAt provenance.vals owner := rfl

theorem effectStep_ownerBorrow (module : GIR.Module) (vt : Array (Option VTy))
    (func : Func) (provenance : Prov) (effect : Core.Eff) (result owner : ValueId) :
    func.effectStep module vt provenance effect (.def result (.ownerBorrow owner)) = effect := rfl

theorem emitDef_ownerBorrow_refined_witness {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {sourceRoots : List RootRef} {ls final : LS} {le : LEnv}
    {scopeCount : Nat} {block : BlockId} {value owner : ValueId}
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (ownerBound : owner < ls.vals.size)
    (roots : RootsRefine func (rootsAt upper.vals owner) sourceRoots)
    (run : emitDef (.ownerBorrow owner) le ls = (value, final)) :
    ∃ next : Prov, BuilderRootWitness results vt func next final ∧
      BuilderEffectRefinement module vt func next source final ∧
      RootsRefine func (rootsAt next.vals value) sourceRoots ∧ next.slots = upper.slots := by
  obtain ⟨next, rootWitness, effects, resultRoots, slots⟩ :=
    emitDef_refined_witness symbols current blockBound witness prior
      (op := .ownerBorrow owner)
      (by simpa [Op.uses] using ownerBound) (effectRefinement_empty func source) run
  refine ⟨next, rootWitness, effects, ?_, slots⟩
  rw [resultRoots]
  exact roots

end Goose.Lower.Validation.SummaryPreservation
