import Goose.Proofs.ConstructionAcceptedTypingDeclaration

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem rpStmt_byteOwner_cursor (env : PEnv) (id : Nat) (bytes : List UInt8)
    (origin bytesOrigin : Goose.Core.OriginId) (before after : RState) (descriptor : LocalVar)
    (declared : env.impl.vars[id]? = some descriptor) (ty : descriptor.ty = .varr (.int .u8))
    (fits : bytes.length < 2 ^ 32)
    (checked : rpStmt env (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .ok ((), after)) :
    after = { before with nextVar := before.nextVar + 1 } := by
  have order := (rpStmt_letS_initializer checked).1
  subst id
  simp only [rpStmt, bind, StateT.bind] at checked
  have getState (state : RState) : (get : P RState) state = .ok (state, state) := rfl
  have modifyState (f : RState → RState) (state : RState) : (modify f : P Unit) state = .ok ((), f state) := rfl
  simp only [getState, Except.bind, ↓reduceIte] at checked
  simp only [StateT.bind, modifyState, rpExpr, pure, declared, ty, Ty.isRefLike] at checked
  simp only [StateT.pure, Bool.false_eq_true, ↓reduceIte] at checked
  simp only [bind, Except.bind, pure] at checked
  dsimp only [Except.pure] at checked
  have bounded : ¬ bytes.length > 2 ^ 32 - 1 := by omega
  simp only [noteReceivingCapacity_byte_result, bounded, ↓reduceIte] at checked
  change Except.ok ((), { before with nextVar := before.nextVar + 1 }) = Except.ok ((), after) at checked
  cases checked
  rfl

#print axioms rpStmt_byteOwner_cursor

end Goose.Proofs.ConstructionAcceptedExecution
