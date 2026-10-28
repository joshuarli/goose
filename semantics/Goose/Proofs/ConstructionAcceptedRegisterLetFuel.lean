import Goose.Proofs.ConstructionAcceptedRegisterInitializerPosition

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem SourcePosition.registerLet_fuel {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (localId statementOrigin contextId origin : Nat) (expression : Expr)
    (context : Context) (helper : Impl)
    (compatible : SourceFrameCompatible accepted frame)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (position : SourcePosition accepted frame (.statement (.letS localId (.call contextId [.byVal expression] origin) statementOrigin))) :
    ∃ checkFuel, frame.typingFuel = checkFuel + 3 := by
  obtain ⟨_, _, _, typed, _⟩ := position.checked accepted frame _
  cases nesting : frame.typingFuel with
  | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
  | succ first =>
    obtain ⟨descriptor, declared, typingOrder, rootOrder, callPosition⟩ :=
      position.registerCallInitializer frame localId statementOrigin contextId origin first expression nesting
    obtain ⟨types, after, roots, rootsAfter, callTyped, callRooted⟩ := callPosition.checked accepted _ _
    cases first with
    | zero => change Except.error _ = Except.ok _ at callTyped; cases callTyped
    | succ second =>
      cases second with
      | zero =>
        let initial := letInitializerFrame frame localId 1
        have ctx : initial.typing.module.contexts[contextId]? = some context := by
          simpa [initial, letInitializerFrame, ordinaryOperandFrame, compatible.module] using contextAt
        have callee : initial.typing.module.impls[context.impl]? = some helper := by
          simpa [initial, letInitializerFrame, ordinaryOperandFrame, compatible.module] using helperAt
        obtain ⟨middle, arguments⟩ := typeExpr_call_arguments 0 initial.typing contextId context helper [.byVal expression]
          origin initial.typingCounter after types ctx callee callTyped
        change Except.error _ = Except.ok _ at arguments
        cases arguments
      | succ checkFuel => exact ⟨checkFuel, by omega⟩

#print axioms SourcePosition.registerLet_fuel
end Goose.Proofs.ConstructionAcceptedExecution
