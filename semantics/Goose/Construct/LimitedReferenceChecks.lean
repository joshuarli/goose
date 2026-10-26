import Goose.Construct.Typing

namespace Goose.Construct.LimitedReferenceChecks

private def limited : Ty := .limited (.int .i64) 4
private def module : Module := ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩
private def environment (ty : Ty) : TypingEnv :=
  ⟨module, none, #[⟨"owner", ty, .immutable, 0, 0⟩], [0], 0, 0, .ordinary, .value, [], none, 0⟩
private def callee (mutability : Goose.Core.Mutability) : Impl :=
  ⟨"borrow", #[⟨0, .byRef⟩], #[], #[⟨"owner", .ref mutability limited, .immutable, 0, 0⟩],
    .mk 0 [] none, .unknown⟩
private def acceptsReference (mutability : Goose.Core.Mutability) (ty : Ty) (place : Place) : Bool :=
  (typeExpr 32 (environment ty) (.ref mutability place) 0).isOk
private def acceptsArgument (mutability : Goose.Core.Mutability) (ty : Ty) (place : Place) : Bool :=
  let target := callee mutability
  (typeArguments 32 (environment ty) target target.params.toList [.byRef mutability place] 0).isOk

#guard acceptsReference .mutable limited (.var 0)
#guard acceptsArgument .mutable limited (.var 0)
#guard !acceptsReference .mutable (.ref .readOnly limited) (.deref (.read (.var 0)))
#guard !acceptsArgument .mutable (.ref .readOnly limited) (.deref (.read (.var 0)))
#guard acceptsReference .readOnly (.ref .readOnly limited) (.deref (.read (.var 0)))
#guard acceptsArgument .readOnly (.ref .readOnly limited) (.deref (.read (.var 0)))

end Goose.Construct.LimitedReferenceChecks
