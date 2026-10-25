import Goose.Lower.Validation.PermissionPreservationContents

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem readRecipe_preservesTables (value : ValueId) (place : Place) (le : LEnv)
    (before : LS) :
    (recordReadValueRootRecipe value place le before).2.blocks = before.blocks ∧
      (recordReadValueRootRecipe value place le before).2.vals = before.vals := by
  cases place with
  | var variableId =>
    simp only [recordReadValueRootRecipe_run]
    split <;> simp [recordValueRootSource_run]
  | global _ => simp [recordReadValueRootRecipe_run]
  | deref _ => simp [recordReadValueRootRecipe_run]
  | elem _ _ _ => simp [recordReadValueRootRecipe_run]
  | field _ _ => simp [recordReadValueRootRecipe_run]

private theorem writableEvidence_after_read_recipe {le : LEnv} {before after : LS}
    {value : ValueId} {place : Place}
    (evidence : WritableEvidence le before value)
    (run : recordReadValueRootRecipe value place le before = ((), after)) :
    WritableEvidence le after value := by
  obtain ⟨blocks, vals⟩ := readRecipe_preservesTables value place le before
  have recordedBlocks := congrArg (fun result : Unit × LS => result.2.blocks) run
  have recordedVals := congrArg (fun result : Unit × LS => result.2.vals) run
  have afterBlocks : after.blocks = before.blocks := recordedBlocks.symm.trans blocks
  have afterVals : after.vals = before.vals := recordedVals.symm.trans vals
  simpa [WritableEvidence, permissionFunc, afterBlocks, afterVals] using evidence

theorem writableEvidence_load {le : LEnv} {before after : LS}
    {owner value : ValueId} {referent : Ty} {current : BlockId}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (run : emitDef (.load owner) le before = (value, after))
    (typed : after.vals[value]? = some (some (.data (.ref .mutable referent)))) :
    WritableEvidence le after value := by
  apply writableEvidence_fresh_definition checked bounded live run
    (ContentsClosed.empty _ _ _ _) (NonIntegerParameters.empty _)
  simp only [WritableOperation, typedPermissions, typed]
  rfl

theorem writableEvidence_call {le : LEnv} {before after : LS}
    {callee : FnId} {args : List ValueId} {origin : Option OriginId}
    {value : ValueId} {referent : Ty} {current : BlockId}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current)
    (run : emitDef (.call callee args origin) le before = (value, after))
    (typed : after.vals[value]? = some (some (.data (.ref .mutable referent)))) :
    WritableEvidence le after value := by
  apply writableEvidence_fresh_definition checked bounded live run
    (ContentsClosed.empty _ _ _ _) (NonIntegerParameters.empty _)
  simp only [WritableOperation, typedPermissions, typed]
  rfl

theorem lowerExpr_read_binding_evidence_of_place {le : LEnv} {place : Place}
    {before middle after : LS} {owner value : ValueId} {referent : Ty} {current : BlockId}
    (placeRun : lowerPlace place le before = (owner, middle))
    (checked : middle.DenseDefinitions) (bounded : LiveBound middle)
    (live : middle.cur = some current)
    (run : lowerExpr (.read place) le before = (value, after))
    (typed : after.vals[value]? = some (some (.data (.ref .mutable referent)))) :
    WritableEvidence le after value := by
  simp only [lowerExpr, bind_run, placeRun] at run
  obtain ⟨valueRun, afterRun⟩ := pure_eq.mp run
  subst value
  let loaded := emitDef (.load owner) le middle
  have recorded : recordReadValueRootRecipe loaded.1 place le loaded.2 = ((), after) := by
    cases result : recordReadValueRootRecipe loaded.1 place le loaded.2 with
    | mk unitValue state =>
      cases unitValue
      have stateEq : state = after := by simpa [result, loaded] using afterRun
      rw [← stateEq]
  obtain ⟨_, vals⟩ := readRecipe_preservesTables loaded.1 place le loaded.2
  have recordedVals := congrArg (fun result : Unit × LS => result.2.vals) recorded
  have afterVals : after.vals = loaded.2.vals := recordedVals.symm.trans vals
  have typedLoad : loaded.2.vals[loaded.1]? = some (some (.data (.ref .mutable referent))) := by
    rw [← afterVals]
    exact typed
  have loadEvidence := writableEvidence_load checked bounded live (show
    emitDef (.load owner) le middle = (loaded.1, loaded.2) from rfl) typedLoad
  exact writableEvidence_after_read_recipe loadEvidence recorded

#print axioms writableEvidence_load
#print axioms writableEvidence_call
#print axioms lowerExpr_read_binding_evidence_of_place

end Goose.Lower.Validation
