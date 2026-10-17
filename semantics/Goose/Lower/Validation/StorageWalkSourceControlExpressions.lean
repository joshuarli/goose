import Goose.Lower.Validation.StorageWalkSourceCollections
import Goose.Lower.Validation.StorageWalkControlJoin

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem storageWalk_source_and {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (left right : Expr) (leftChild : StorageWalkSourceExpression env results stack left)
    (rightChild : StorageWalkSourceExpression env results stack right) :
    StorageWalkSourceExpression env results stack (.and left right) := by
  intro type start finish source visible loop
  obtain ⟨leftType, leftFinish, leftSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨checked, rightStart, leftBool, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨rightType, rightFinish, rightSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  exact (leftChild leftSource visible loop).bind fun value =>
    StorageWalkAction.shortCircuit true value (rightChild rightSource visible loop)

theorem storageWalk_source_or {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (left right : Expr) (leftChild : StorageWalkSourceExpression env results stack left)
    (rightChild : StorageWalkSourceExpression env results stack right) :
    StorageWalkSourceExpression env results stack (.or left right) := by
  intro type start finish source visible loop
  obtain ⟨leftType, leftFinish, leftSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨checked, rightStart, leftBool, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨rightType, rightFinish, rightSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  exact (leftChild leftSource visible loop).bind fun value =>
    StorageWalkAction.shortCircuit false value (rightChild rightSource visible loop)

theorem storageWalk_source_ifExpression {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (condition : Expr) (yes no : Core.Block) (conditionChild : StorageWalkSourceExpression env results stack condition)
    (yesChild : ∀ env, StorageWalkSourceBlock env results stack yes)
    (noChild : ∀ env, StorageWalkSourceBlock env results stack no) :
    StorageWalkSourceExpression env results stack (.ifE condition yes no) := by
  intro type start finish source visible loop
  obtain ⟨conditionType, conditionFinish, conditionSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨checked, yesStart, conditionBool, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨yesType, yesFinish, yesSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨noType, noFinish, noSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  exact (conditionChild conditionSource visible loop).bind fun value =>
    StorageWalkAction.ifValue value (sourceBlockScope yes)
      ((storageWalk_source_emptyBlock (yesChild (Core.exprEnv env)) yesSource visible none true).weakenLoop loop)
      ((storageWalk_source_emptyBlock (noChild (Core.exprEnv env)) noSource visible none true).weakenLoop loop)

theorem storageWalk_source_blockExpression {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (body : Core.Block) (child : ∀ env, StorageWalkSourceBlock env results stack body) :
    StorageWalkSourceExpression env results stack (.blockE body) := by
  intro type start finish source visible loop
  exact (storageWalk_source_emptyBlock (child (Core.exprEnv env)) source visible none true).weakenLoop loop

#print axioms storageWalk_source_and
#print axioms storageWalk_source_or
#print axioms storageWalk_source_ifExpression
#print axioms storageWalk_source_blockExpression

end Goose.Lower.Validation
