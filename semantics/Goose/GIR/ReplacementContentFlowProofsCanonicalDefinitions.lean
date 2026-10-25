import Goose.GIR.ReplacementContentFlowProofsCanonicalDefinitionTyping

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem BackingOp.source_used {op : Op} {source : ValueId} (backing : BackingOp op source) :
    source ∈ op.uses := by
  cases backing <;> simp [Op.uses]

theorem State.CanonicalWithin.noncallDefinition {module : Module} {states : Array State}
    {results : Array (List RootRef)} {func : Func} {vt : Array (Option VTy)}
    {provenance : Prov} {state : State} {value : ValueId} {op : Op} {type : VTy} {env : TyEnv}
    (before : state.CanonicalWithin func vt provenance)
    (typed : DefinitionTyping env op type) (canonical : vt[value]? = some (some type))
    (envValues : env.vals = vt) (envSlots : env.slots = func.slots)
    (ordinary : ∀ fn args origin, op ≠ .call fn args origin)
    (unique : (func.roots.contents.toList.map Prod.fst).Nodup)
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (uses : ∀ source ∈ op.uses, source < func.numValues)
    (bounded : value < provenance.vals.size)
    (quiet : func.provStep results vt (provenance,false) (.def value op) = (provenance,false))
    (observed : ∀ source, op = .load source → type.refLike = true →
      ∀ index, RootRef.param index ∈ rootsAt provenance.vals source →
        (func.params[index]?).any Ty.isRefSlice = true →
        (func.roots.contents.find? (·.1 == index)).isSome = true) :
    (step module states func vt state (.def value op)).CanonicalWithin func vt provenance := by
  have sourceBound : ∀ source ∈ op.uses, source < state.values.size := by
    intro source member
    rw [before.shape.values]
    exact uses source member
  cases typed with
  | scalar _ _ _ scalar =>
      apply before.scalarDef ordinary
      simp [valRefLike,canonical,scalar]
  | slot index storage mutability row =>
      exact before.slotAddr (by simpa [envSlots] using row) canonical bounded quiet
  | global index type kind mutability row storage =>
      exact before.globalAddr canonical storage bounded quiet
  | load source mutability payload reference =>
      have sourceType : vt[source]? = some (some (.data (.ref mutability payload))) := by
        simpa [envValues] using TyEnv.refTy_known reference
      exact before.load unique parameters canonical sourceType
        (sourceBound source (by simp [Op.uses])) bounded quiet (observed source rfl)
  | freeze source mutability payload reference =>
      have sourceType : vt[source]? = some (some (.data (.ref mutability payload))) := by
        simpa [envValues] using TyEnv.refTy_known reference
      exact before.refFreeze canonical sourceType (sourceBound source (by simp [Op.uses])) bounded quiet
  | borrow source mutability payload reference owner =>
      have sourceType : vt[source]? = some (some (.data (.ref mutability payload))) := by
        simpa [envValues] using TyEnv.refTy_known reference
      exact before.ownerBorrow canonical sourceType owner (sourceBound source (by simp [Op.uses])) bounded quiet
  | backing op source type backing target =>
      by_cases like : valRefLike vt value = true
      · apply before.forwardBacking (backing.noncall) (backing.result like) backing.rootsOfDef
          (fun mutability payload actual => target mutability payload (by
            rw [canonical] at actual
            exact Option.some.inj (Option.some.inj actual)))
          (sourceBound source backing.source_used) bounded quiet
      · exact before.scalarDef ordinary (Bool.eq_false_iff.mpr like)
  | call fn args origin _ => exact False.elim (ordinary fn args origin rfl)

#print axioms State.CanonicalWithin.noncallDefinition

end Goose.GIR.ReplacementContentFlow.Model
