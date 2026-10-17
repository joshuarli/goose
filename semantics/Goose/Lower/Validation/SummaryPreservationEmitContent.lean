import Goose.Lower.Validation.SummaryPreservationContentReads
import Goose.Lower.Validation.SummaryPreservationRefinedEffects

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitDef_content_read_source_witness {env : PEnv} {context : ContextId}
    {index : Nat} {param : Param} {localVar : LocalVar}
    {sourceRoots : List RootRef} {initial before after : RState}
    {res : Array (List RootRef)} {vt : Array (Option VTy)} {upper : Prov}
    {ls final : LS} {le : LEnv} {scopeCount : Nat} {block : BlockId}
    {value address : ValueId} {mu : Mutability} {element : Ty}
    (accepted : Core.validate env.mod = .ok ())
    (contextLookup : env.mod.contexts[context]? = some env.ctx)
    (implLookup : env.mod.impls[env.ctx.impl]? = some env.impl)
    (parameter : env.impl.params[index]? = some param)
    (variableRow : env.impl.vars[param.var]? = some localVar)
    (reference : localVar.ty.isRefSlice = true)
    (placeSource : rpPlace env (.deref (.read (.var param.var))) initial =
      .ok ([.param index], before))
    (source : rpExpr env (.read (.deref (.read (.var param.var)))) initial =
      .ok (sourceRoots, after))
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size)
    (witness : BuilderRootWitness res vt (lowerContextAt env.mod env.ctx env.impl) upper ls)
    (prior : BuilderEffectRefinement (lower env.mod) vt
      (lowerContextAt env.mod env.ctx env.impl) upper before.eff ls)
    (addressBound : address < ls.vals.size)
    (addressRoots : rootsAt upper.vals address = [.param index])
    (resultType : vt[ls.vals.size]? = some (some (.data (.slice mu element))))
    (run : emitDef (.load address) le ls = (value, final)) :
    ∃ next : Prov,
      BuilderRootWitness res vt (lowerContextAt env.mod env.ctx env.impl) next final ∧
      BuilderEffectRefinement (lower env.mod) vt
        (lowerContextAt env.mod env.ctx env.impl) next after.eff final ∧
      RootsRefine (lowerContextAt env.mod env.ctx env.impl)
        (rootsAt next.vals value) sourceRoots ∧ next.slots = upper.slots := by
  change (do
    let roots ← rpPlace env (.deref (.read (.var param.var)))
    addReads roots
    readRoots env (.deref (.read (.var param.var)))) initial = .ok (sourceRoots, after) at source
  obtain ⟨placeRoots, middle, place, tail⟩ := (st_bind_ok _ _ _ _).mp source
  rw [placeSource] at place
  cases place
  obtain ⟨_, afterReads, reads, readRootsSource⟩ := (st_bind_ok _ _ _ _).mp tail
  have sameState : after = afterReads := (readRoots_ok _ _ _ _ readRootsSource).1
  subst after
  let func := lowerContextAt env.mod env.ctx env.impl
  have closed := lowerContextAt_parameterRoots_closed accepted contextLookup implLookup
  have priorFinal : BuilderEffectRefinement (lower env.mod) vt func upper afterReads.eff ls := by
    intro inst member
    exact (prior inst member).source_mono
      (PMono.addReads _ _ _ _ reads).2 (PMonoRebinds.addReads _ _ _ _ reads)
      (PFlagsMono.addReads _ _ _ _ reads)
  have rootsRefine : RootsRefine func
      (rootsOfDef res vt func upper ls.vals.size (.load address)) sourceRoots :=
    readRoots_refSlice_parameter_refines parameter variableRow reference readRootsSource
      addressRoots resultType
  have delta : EffectRefinement func
      (func.effectStep (lower env.mod) vt upper {} (.def ls.vals.size (.load address)))
      afterReads.eff := by
    apply effectStep_load_refines_from_source closed (effectRefinement_empty func before.eff) _ reads
    rw [addressRoots]
    exact RootsRefine.refl _ _
  obtain ⟨next, rootWitness, effects, resultRoots, slots⟩ :=
    emitDef_refined_witness symbols current blockBound witness priorFinal
      (by simpa [Op.uses] using addressBound) delta run
  refine ⟨next, rootWitness, effects, ?_, slots⟩
  rw [resultRoots]
  have valueEq : value = ls.vals.size := by
    rw [emitDef_run _ _ current] at run
    exact (Prod.mk.inj run).1.symm
  rw [valueEq]
  exact rootsRefine

end Goose.Lower.Validation.SummaryPreservation
