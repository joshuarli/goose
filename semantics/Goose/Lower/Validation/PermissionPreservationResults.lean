import Goose.Lower.Validation.PermissionPreservationContents

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

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
  exact writableEvidence_load checked bounded live run typed

#print axioms writableEvidence_load
#print axioms writableEvidence_call
#print axioms lowerExpr_read_binding_evidence_of_place

end Goose.Lower.Validation
