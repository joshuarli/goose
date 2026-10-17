import Goose.Lower.Validation.ScopeFlowSource
import Goose.Lower.Validation.ScopeFinish

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ScopeFlowAction.emitReturn (parents : Array (Option ScopeId))
    (loop : Option LoopCtx) (values : List ValueId) (origin : Option OriginId) :
    ScopeFlowAction parents none loop (Goose.Lower.emitTerm (.ret values origin)) := by
  refine ⟨ScopeAction.emitReturn parents values origin, ?_⟩
  intro env before entry exit config context head
  have empty : before.stack = [] := by
    cases stack : before.stack with
    | nil => rfl
    | cons scope rest => simp [stack] at head
  have unwound := (ScopeFlowAction.unwindReturn parents none loop values origin).preserves
    env before entry exit config context head
  simpa only [bind_run, leaveTo, get_apply, empty, List.length_nil, Nat.sub_self,
    List.take_zero, leaveAll, pure_run] using unwound

theorem ScopeFlowAction.finishFunction (parents : Array (Option ScopeId)) (impl : Impl) (value : ValueId) :
    ScopeFlowAction parents none none (Goose.Lower.finishFunction impl value) := by
  unfold Goose.Lower.finishFunction
  refine (ScopeFlowAction.read parents none none).bind fun env =>
    (ScopeFlowAction.isLive parents none none).bind fun live => ?_
  cases live <;> simp only [Bool.false_eq_true, reduceIte]
  · exact ScopeFlowAction.pure parents none none _
  · split
    · apply ScopeFlowAction.header [] [] advB_newBlock0
        (fun sink _ => Goose.Lower.emitTerm (.br sink []))
        (fun sink _ => ScopeAction.emitNeutralTerm parents none (.br sink []) rfl)
      intro sink params env before entry exit config context head current target bound result after run
      have closed := config.emitTerm (.br sink []) rfl env (by
        intro destination member
        have same : destination = sink := by simpa [Term.successors] using member
        subst destination
        exact target) (by
        intro destination member
        have same : destination = sink := by simpa [Term.successors] using member
        subst destination
        exact bound)
      rw [run] at closed
      exact ⟨entry, exit, closed, ScopeMapAdvance.refl _ _ _⟩
    · exact ScopeFlowAction.emitReturn parents none _ none

theorem scopeInitialState_configuration (parents : Array (Option ScopeId)) (env : LEnv) (types : List VTy) :
    ScopeConfiguration parents (fun _ => []) (fun _ => []) (scopeInitialState env types) := by
  refine ⟨scopeInitialState_valid parents env types, ?_, ?_, ?_⟩
  · intro block current
    have equal : 0 = block := Option.some.inj current
    subst block
    exact ⟨_, by rfl, by rfl⟩
  · intro block body row target member
    have bound := (Array.getElem?_eq_some_iff.mp row).1
    have zero : block = 0 := by have size := scopeInitialState_size env types; nat_omega
    subst block
    have same : body = (scopeInitialState env types).blocks[0] :=
      (Array.getElem?_eq_some_iff.mp row).2.symm
    subst body
    change target ∈ ([] : List BlockId) at member
    cases member
  · intro block body row target member
    rfl

theorem scopeImplTail_flow (parents : Array (Option ScopeId)) (impl : Impl)
    (parameters : List ValueId) (source : ScopeTableContains parents (blockScopes none impl.body)) :
    ScopeFlowAction parents none none (scopeImplTail impl parameters) := by
  unfold scopeImplTail
  exact (scopeFlow_lowerBlock parents none none _ false impl.body source).bind fun value =>
    ScopeFlowAction.finishFunction parents impl value

theorem lowerImpl_scopeGraph {module : Core.Module} {impl : Impl}
    (checked : checkImpl module impl = .ok ()) : Nonempty (ScopeGraph (lowerImpl module impl)) := by
  let env := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun parameter => VTy.data (tyOfVar impl parameter.var)
  let parameters := (newBlock types env initState).1.2
  let initial := scopeInitialState env types
  let action := scopeImplTail impl parameters
  let parents := (lowerImpl module impl).scopes
  have source := lowerImpl_lexicalScopeTable checked
  have actionFlow := scopeImplTail_flow parents impl parameters source
  obtain ⟨entry, exit, config, framed⟩ := actionFlow.preserves env initial
    (fun _ => []) (fun _ => []) (scopeInitialState_configuration parents env types) trivial rfl
  have initialEntry : entry 0 = [] := (framed 0 (by rw [scopeInitialState_size]; decide)).1
  exact ⟨config.builder.finish initialEntry config.edges (lowerImpl module impl) rfl rfl⟩

theorem lowerContextAt_scopeGraph {module : Core.Module} {impl : Impl}
    (checked : checkImpl module impl = .ok ()) (context : Context) :
    Nonempty (ScopeGraph (lowerContextAt module context impl)) := by
  obtain ⟨graph⟩ := lowerImpl_scopeGraph checked
  exact ⟨⟨graph.entry, graph.exit, graph.initial,
    by simpa only [lowerContextAt_scopes, lowerContextAt_blocks] using graph.trace,
    by simpa only [lowerContextAt_blocks] using graph.edge⟩⟩

theorem lowerGlobal_scopeGraph {module : Core.Module} {index : GlobalId} {global : Core.Global}
    (checked : checkGlobal module index global = .ok ()) :
    Nonempty (ScopeGraph (lowerGlobal module global).init) := by
  let env := lowerEnv module #[] [global.ty]
  let initial := scopeInitialState env []
  let action := scopeGlobalTail global
  let parents := (lowerGlobal module global).init.scopes
  have source := lowerGlobal_lexicalScopeTable checked
  have actionFlow : ScopeFlowAction parents none none action :=
    (scopeFlow_lowerExpr parents none none global.init source).bind fun value =>
      ScopeFlowAction.emitReturn parents none [value] (some global.org)
  obtain ⟨entry, exit, config, framed⟩ := actionFlow.preserves env initial
    (fun _ => []) (fun _ => []) (scopeInitialState_configuration parents env []) trivial rfl
  have initialEntry : entry 0 = [] := (framed 0 (by rw [scopeInitialState_size]; decide)).1
  exact ⟨config.builder.finish initialEntry config.edges (lowerGlobal module global).init rfl rfl⟩

theorem lowerImpl_walkScopes {module : Core.Module} {impl : Impl}
    (checked : checkImpl module impl = .ok ()) (label : String) :
    (walkScopes label (lowerImpl module impl)).scopes = none := by
  obtain ⟨graph⟩ := lowerImpl_scopeGraph checked
  exact graph.walkScopes label

theorem lowerContextAt_walkScopes {module : Core.Module} {impl : Impl}
    (checked : checkImpl module impl = .ok ()) (context : Context) (label : String) :
    (walkScopes label (lowerContextAt module context impl)).scopes = none := by
  obtain ⟨graph⟩ := lowerContextAt_scopeGraph checked context
  exact graph.walkScopes label

theorem lowerGlobal_walkScopes {module : Core.Module} {index : GlobalId} {global : Core.Global}
    (checked : checkGlobal module index global = .ok ()) (label : String) :
    (walkScopes label (lowerGlobal module global).init).scopes = none := by
  obtain ⟨graph⟩ := lowerGlobal_scopeGraph checked
  exact graph.walkScopes label

end Goose.Lower.Validation
