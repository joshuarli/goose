import Goose.Proofs.ConstructionAcceptedScalarStatement

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem SourcePosition.scalarHeadEffects {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (expression : Expr) (origin : Goose.Core.OriginId) (rest : List Stmt)
    (position : SourcePosition accepted frame (.statements (.expr expression origin :: rest)))
    (available : ∀ rootsAfter, rpStmts frame.source (.expr expression origin :: rest) frame.rootCursor = .ok ((), rootsAfter) →
      GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff) :
    ∃ roots middle rootsAfter, rpExpr frame.source expression frame.rootCursor = .ok (roots, middle) ∧
      rpStmt frame.source (.expr expression origin) frame.rootCursor = .ok ((), middle) ∧
      rpStmts frame.source rest middle = .ok ((), rootsAfter) ∧
      GlobalEffectsAvailable frame.interpretation frame.initialized middle.eff := by
  obtain ⟨_, _, rootsAfter, _, rooted⟩ := position.checked accepted frame _
  obtain ⟨middle, head, tail⟩ := rpStmts_cons rooted
  obtain ⟨roots, expressionRooted⟩ := rpStmt_expression head
  have included := rpStmts_effectTargetsIncluded tail
  have headAvailable : GlobalEffectsAvailable frame.interpretation frame.initialized middle.eff := by
    intro target member global instantiates
    exact available rootsAfter rooted target (included member) global instantiates
  exact ⟨roots, middle, rootsAfter, expressionRooted, head, tail, headAvailable⟩

theorem SourcePosition.zeroInitializationUnavailable {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (action : SourceAction)
    (position : SourcePosition accepted frame action) (effects : Eff) (id : Nat)
    (read : .global id ∈ effects.reads) :
    SourcePosition accepted { frame with initialized := 0 } action ∧
      ¬ GlobalEffectsAvailable frame.interpretation 0 effects := by
  refine ⟨position.instantiate frame.interpretation 0, ?_⟩
  intro available
  have impossible := available (.global id) (by simp [read]) id rfl
  change id < 0 at impossible
  omega

theorem SourcePosition.zeroInitializationGlobalRead {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (id : Nat)
    (position : SourcePosition accepted frame (.expression (.read (.global id)))) :
    ∃ roots rootsAfter,
      SourcePosition accepted { frame with initialized := 0 } (.expression (.read (.global id))) ∧
      rpExpr frame.source (.read (.global id)) frame.rootCursor = .ok (roots, rootsAfter) ∧
      ¬ GlobalEffectsAvailable frame.interpretation 0 rootsAfter.eff := by
  obtain ⟨_, _, roots, rootsAfter, _, provenance⟩ := position.checked accepted frame _
  have extracted := congrArg
    (fun result : Except Goose.Core.Rejection (List RootRef × RState) =>
      result.toOption.map (fun pair => pair.2.eff.reads)) provenance
  change some (addTargets frame.rootCursor.eff.reads [.global id]) = some rootsAfter.eff.reads at extracted
  have reads := (Option.some.inj extracted).symm
  have member : Goose.Construct.Target.global id ∈ rootsAfter.eff.reads := by
    rw [reads]
    simp only [addTargets, List.foldl_cons, List.foldl_nil]
    split <;> simp_all
  have result := position.zeroInitializationUnavailable accepted frame (.expression (.read (.global id))) rootsAfter.eff id member
  exact ⟨roots, rootsAfter, result.1, provenance, result.2⟩

#print axioms SourcePosition.zeroInitializationGlobalRead
#print axioms SourcePosition.scalarHeadEffects
#print axioms SourcePosition.zeroInitializationUnavailable
end Goose.Proofs.ConstructionAcceptedExecution
