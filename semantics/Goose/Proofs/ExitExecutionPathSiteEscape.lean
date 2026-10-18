import Goose.Proofs.ExitExecutionPathDeliveryControl
import Goose.Proofs.ExitExecutionPathSiteStop
import Goose.Proofs.ExitExecutionPathDispatchUnwind
import Goose.Proofs.ExitExecutionPathSequenceUnwind
import Goose.Proofs.ExitExecutionPathProducerUnwind
import Goose.Proofs.ExitExecutionPathUnwindControl
import Goose.Proofs.ExitExecutionPathControlUnwind
import Goose.Proofs.ExitExecutionPathCompletionUnwind
import Goose.Proofs.ExitExecutionPathScopeForward
import Goose.Proofs.ExitExecutionPathOutsideScopeReads

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

private def nativeScopeObjects (parent : ExitInvocation α) (initial before final : ExecutionState) : Prop :=
  match parent with
  | .block _ environment _ _ (.mk scope _ _)
  | .activationScope _ environment _ (.mk scope _ _)
  | .resultScope _ environment _ _ (.mk scope _ _) =>
      final.objects = (releaseScopeState environment scope initial.nextScope before).objects
  | _ => final.objects = before.objects

private def nativeHandlerCatch (config : EvalConfig) (parent : ExitInvocation α)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (before final : ExecutionState) : Prop :=
  match parent with
  | .activation (fuel + 1) activation pre body origin =>
      address.activation = activation.act ∧
      execActivationBody fuel config activation pre body initial = .escape address carriers before ∧
      enterActivation (fuel + 1) config activation pre body origin initial = .ok carriers final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects
  | _ => False

private theorem escapeFrame_exact {config : EvalConfig} {α β : Type}
    {parent : ExitInvocation α} {child : ExitInvocation β} {initial prepared : ExecutionState}
    (_site : ExitCallSite config parent initial child prepared)
    (before : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : parent.action config initial = .escape address carriers before)
    (objects : nativeScopeObjects parent initial before before) :
    (∃ final, parent.action config initial = .escape address carriers final ∧
      final.construction.stdout = before.construction.stdout ∧ nativeScopeObjects parent initial before final) ∨
    (∃ reason final, parent.action config initial = .stop reason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects) ∨
    (∃ final, nativeHandlerCatch config parent initial address carriers before final) :=
  Or.inl ⟨before, escaped, rfl, objects⟩

private theorem ExitCallSite.escape_after_child {config : EvalConfig} {α β : Type}
    {parent : ExitInvocation α} {child : ExitInvocation β}
    {initial prepared before : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    (site : ExitCallSite config parent initial child prepared)
    (escaped : child.action config prepared = .escape address carriers before) :
    (∃ final, parent.action config initial = .escape address carriers final ∧
      final.construction.stdout = before.construction.stdout ∧ nativeScopeObjects parent initial before final) ∨
    (∃ reason final, parent.action config initial = .stop reason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects) ∨
    (∃ final, nativeHandlerCatch config parent initial address carriers before final) := by
  have actualSite := site
  cases site
  case values edge =>
    refine Or.inl ⟨before, edge.escape address carriers before escaped, rfl, ?_⟩
    cases edge <;> rfl
  case producer edge =>
    rcases edge.escape_after_child escaped with ⟨final, evaluated, stdout, objects⟩ | ⟨reason, final, evaluated, stdout, objects⟩
    · refine Or.inl ⟨final, evaluated, stdout, ?_⟩
      cases edge <;> exact objects
    · exact Or.inr (Or.inl ⟨reason, final, evaluated, stdout, objects⟩)
  case statements edge =>
    rcases edge.escape_after_child escaped with ⟨final, evaluated, stdout, objects⟩ | ⟨reason, final, evaluated, stdout, objects⟩
    · refine Or.inl ⟨final, evaluated, stdout, ?_⟩
      cases edge <;> exact objects
    · exact Or.inr (Or.inl ⟨reason, final, evaluated, stdout, objects⟩)
  case activationBody =>
    rename_i fuel activation pre body origin implementation lookup
    change execActivationBody fuel config activation pre body initial = .escape address carriers before at escaped
    rcases enterActivation_escape_or_catch fuel config activation pre body origin implementation initial before
      address carriers lookup escaped with ⟨final, evaluated, stdout, objects⟩ | ⟨reason, final, evaluated, stdout, objects⟩ | ⟨final, sameActivation, evaluated, stdout, objects⟩
    · exact Or.inl ⟨final, evaluated, stdout, objects⟩
    · exact Or.inr (Or.inl ⟨reason, final, evaluated, stdout, objects⟩)
    · exact Or.inr (Or.inr ⟨final, sameActivation, escaped, evaluated, stdout, objects⟩)
  case blockStatements =>
    obtain ⟨final, evaluated, released, storage⟩ := ExitCallSite.blockStatements_escape_after_child actualSite (by assumption) escaped
    refine Or.inl ⟨final, evaluated, ?_, ?_⟩ <;> rw [released] <;> rfl
  case blockValueTail =>
    obtain ⟨final, evaluated, released, storage⟩ := ExitCallSite.blockValueTail_escape_after_child actualSite (by assumption) (by assumption) (by assumption) escaped
    refine Or.inl ⟨final, evaluated, ?_, ?_⟩ <;> rw [released] <;> rfl
  case blockProduceTail =>
    obtain ⟨final, evaluated, released, storage⟩ := ExitCallSite.blockProduceTail_escape_after_child actualSite (by assumption) (by assumption) (by assumption) escaped
    refine Or.inl ⟨final, evaluated, ?_, ?_⟩ <;> rw [released] <;> rfl
  case activationStatements =>
    obtain ⟨final, evaluated, released, storage⟩ := ExitCallSite.activationStatements_escape_after_child actualSite (by assumption) escaped
    refine Or.inl ⟨final, evaluated, ?_, ?_⟩ <;> rw [released] <;> rfl
  case activationTail =>
    obtain ⟨final, evaluated, released, storage⟩ := ExitCallSite.activationTail_escape_after_child actualSite (by assumption) (by assumption) escaped
    refine Or.inl ⟨final, evaluated, ?_, ?_⟩ <;> rw [released] <;> rfl
  case resultStatements =>
    obtain ⟨final, evaluated, released, storage⟩ := ExitCallSite.resultStatements_escape_after_child actualSite (by assumption) escaped
    refine Or.inl ⟨final, evaluated, ?_, ?_⟩ <;> rw [released] <;> rfl
  case resultTail =>
    obtain ⟨final, evaluated, released, storage⟩ := ExitCallSite.resultTail_escape_after_child actualSite (by assumption) (by assumption) escaped
    refine Or.inl ⟨final, evaluated, ?_, ?_⟩ <;> rw [released] <;> rfl
  all_goals simp only [ExitInvocation.action] at escaped ⊢
  case returnOperands =>
    rcases returnOperands_escape_after_child _ _ _ _ _ _ _ _ _ _ _ _ (by assumption) (by assumption) escaped with ⟨final, changes, evaluated, stdout, objects, storage⟩ | ⟨reason, final, changes, evaluated, stdout, objects, storage⟩
    · exact Or.inl ⟨final, evaluated, stdout, objects⟩
    · exact Or.inr (Or.inl ⟨reason, final, evaluated, stdout, objects⟩)
  case returnForwardProduce =>
    rcases returnForwardProduce_escape_after_child _ _ _ _ _ _ _ _ _ _ _ _ (by assumption) (by assumption) escaped with ⟨final, changes, evaluated, stdout, objects, storage⟩ | ⟨reason, final, changes, evaluated, stdout, objects, storage⟩
    · exact Or.inl ⟨final, evaluated, stdout, objects⟩
    · exact Or.inr (Or.inl ⟨reason, final, evaluated, stdout, objects⟩)
  case returnProduce =>
    rcases returnProduce_escape_after_child _ _ _ _ _ _ _ _ _ _ _ _ (by assumption) (by assumption) escaped with ⟨final, changes, evaluated, stdout, objects, storage⟩ | ⟨reason, final, changes, evaluated, stdout, objects, storage⟩
    · exact Or.inl ⟨final, evaluated, stdout, objects⟩
    · exact Or.inr (Or.inl ⟨reason, final, evaluated, stdout, objects⟩)
  case returnFromOperands =>
    rcases returnFromOperands_escape_after_child _ _ _ _ _ _ _ _ _ _ _ _ _ (by assumption) (by assumption) escaped with ⟨final, changes, evaluated, stdout, objects, storage⟩ | ⟨reason, final, changes, evaluated, stdout, objects, storage⟩
    · exact Or.inl ⟨final, evaluated, stdout, objects⟩
    · exact Or.inr (Or.inl ⟨reason, final, evaluated, stdout, objects⟩)
  case returnFromForwardProduce =>
    rcases returnFromForwardProduce_escape_after_child _ _ _ _ _ _ _ _ _ _ _ _ _ (by assumption) (by assumption) escaped with ⟨final, changes, evaluated, stdout, objects, storage⟩ | ⟨reason, final, changes, evaluated, stdout, objects, storage⟩
    · exact Or.inl ⟨final, evaluated, stdout, objects⟩
    · exact Or.inr (Or.inl ⟨reason, final, evaluated, stdout, objects⟩)
  case breakProduce =>
    rcases breakProduce_escape_after_child _ _ _ _ _ _ _ _ _ _ _ _ (by assumption) (by assumption) escaped with ⟨final, changes, evaluated, stdout, objects, storage⟩ | ⟨reason, final, changes, evaluated, stdout, objects, storage⟩
    · exact Or.inl ⟨final, evaluated, stdout, objects⟩
    · exact Or.inr (Or.inl ⟨reason, final, evaluated, stdout, objects⟩)
  case completionProduce =>
    rename_i fuel environment incoming expression planned setup
    rcases completionProduce_escape_after_child incoming (expressionOrigin expression)
      (fun channels => evalProduce fuel config environment channels expression)
      initial prepared before planned address carriers setup escaped with ⟨final, changes, evaluated, stdout, objects, storage⟩ | ⟨reason, final, changes, evaluated, stdout, objects, storage⟩
    · exact Or.inl ⟨final, evaluated, stdout, objects⟩
    · exact Or.inr (Or.inl ⟨reason, final, evaluated, stdout, objects⟩)
  all_goals first
    | (apply escapeFrame_exact actualSite
       · first
           | (apply moduleGlobals_escape_after_child <;> assumption)
           | (apply moduleEntry_escape_after_child <;> assumption)
           | (apply CallArgumentPrefix.escape_call <;> assumption)
           | (apply CallActivationPrefix.escape_call <;> assumption)
           | (apply argumentReference_escape_after_child <;> assumption)
           | (apply argumentValue_escape_after_child <;> assumption)
           | (apply argumentMaterialize_escape_after_child <;> assumption)
           | (apply argumentBuild_escape_after_child <;> assumption)
           | (apply ArgumentValuePrefix.escape_arguments <;> assumption)
           | (apply operandsHead_escape_after_child <;> assumption)
           | (apply operandsTail_escape_after_child <;> assumption)
           | (apply statementsHead_escape_after_child <;> assumption)
           | (apply statementsTail_escape_after_child <;> assumption)
           | (apply activationScope_escape_after_child <;> assumption)
           | (apply resultBlockWith_escape_after_child <;> assumption)
           | (apply resultScope_escape_after_child <;> assumption)
       · rfl)

private def scopeRootsAvoid (context : List ExitLexicalFrame) (root : Goose.Core.RootInst) : Prop :=
  ∀ environment scope scopeInst, ExitLexicalFrame.scope environment scope scopeInst ∈ context →
    (Goose.Proofs.Exit.runtimeScopeRoots environment scope scopeInst).contains root = false

private theorem ExitCallSite.scope_objects_added {config : EvalConfig} {α β : Type}
    {parent : ExitInvocation α} {child : ExitInvocation β}
    {initial prepared before final : ExecutionState} {outer inner added : List ExitLexicalFrame}
    (site : ExitCallSite config parent initial child prepared) (frames : site.frames outer inner)
    (shape : inner = added ++ outer) (objects : nativeScopeObjects parent initial before final)
    (root : Goose.Core.RootInst) (outside : scopeRootsAvoid added root) :
    final.objects.lookup root = before.objects.lookup root := by
  cases parent
  all_goals try exact congrArg (fun entries => entries.lookup root) objects
  case block fuel environment pre channels body =>
    cases body
    dsimp only [ExitCallSite.frames, ExitInvocation.frames] at frames
    have same : added = [.scope environment _ initial.nextScope] :=
      List.append_cancel_right (shape.symm.trans frames)
    rw [objects]
    apply releaseScopeState_root_lookup
    apply outside
    rw [same]
    exact List.mem_cons_self
  case activationScope fuel environment pre body =>
    cases body
    dsimp only [ExitCallSite.frames, ExitInvocation.frames] at frames
    have same : added = [.scope environment _ initial.nextScope] :=
      List.append_cancel_right (shape.symm.trans frames)
    rw [objects]
    apply releaseScopeState_root_lookup
    apply outside
    rw [same]
    exact List.mem_cons_self
  case resultScope fuel environment pre channels body =>
    cases body
    dsimp only [ExitCallSite.frames, ExitInvocation.frames] at frames
    have same : added = [.scope environment _ initial.nextScope] :=
      List.append_cancel_right (shape.symm.trans frames)
    rw [objects]
    apply releaseScopeState_root_lookup
    apply outside
    rw [same]
    exact List.mem_cons_self

private theorem handler_act_unique (handlers : List OwnershipActivationChannels)
    (distinct : (handlers.map (·.act)).Nodup)
    (first second : OwnershipActivationChannels)
    (firstMember : first ∈ handlers) (secondMember : second ∈ handlers)
    (same : first.act = second.act) : first = second := by
  induction handlers with
  | nil => cases firstMember
  | cons current rest previous =>
      have splitDistinct := List.nodup_cons.mp distinct
      rcases List.mem_cons.mp firstMember with firstHere | firstTail
      · subst first
        rcases List.mem_cons.mp secondMember with secondHere | secondTail
        · exact secondHere.symm
        · exact False.elim (splitDistinct.1 (List.mem_map.mpr ⟨second, secondTail, same.symm⟩))
      · rcases List.mem_cons.mp secondMember with secondHere | secondTail
        · subst second
          exact False.elim (splitDistinct.1 (List.mem_map.mpr ⟨first, firstTail, same⟩))
        · exact previous splitDistinct.2 firstTail secondTail

private def scopeRootCondition (parent : ExitInvocation α) (initial : ExecutionState) (root : Goose.Core.RootInst) : Prop :=
  match parent with
  | .block _ environment _ _ (.mk scope _ _)
  | .activationScope _ environment _ (.mk scope _ _)
  | .resultScope _ environment _ _ (.mk scope _ _) =>
      (Goose.Proofs.Exit.runtimeScopeRoots environment scope initial.nextScope).contains root = false
  | _ => True

local macro "scope_condition" : tactic => `(tactic|
  simp [scopeRootsAvoid, scopeRootCondition] <;>
    (constructor
     · intro kept
       exact kept _ _ _ rfl rfl rfl
     · intro kept capturedEnvironment capturedScope capturedInst sameEnvironment sameScope sameInst
       subst capturedEnvironment
       subst capturedScope
       subst capturedInst
       exact kept))

private theorem ExitInvocation.frames_scope_prefix {config : EvalConfig} {α : Type}
    {caller : ExitInvocation α} {initial middle : ExecutionState} {outer inner : List ExitLexicalFrame}
    (frames : caller.frames config initial middle outer inner) :
    ∃ added, inner = added ++ outer ∧ ∀ root, scopeRootsAvoid added root ↔ scopeRootCondition caller initial root := by
  cases caller
  all_goals dsimp only [ExitInvocation.frames] at frames
  all_goals first
    | (subst inner; first | (refine ⟨[], rfl, ?_⟩; intro root; scope_condition) | (refine ⟨[_], rfl, ?_⟩; intro root; scope_condition))
    | (rcases frames with ⟨_, _, rfl⟩; (refine ⟨[_], rfl, ?_⟩; intro root; scope_condition))
    | skip
  case activationScope fuel environment pre body =>
    cases body
    dsimp only at frames
    subst inner
    (refine ⟨[_], rfl, ?_⟩; intro root; scope_condition)
  case resultScope fuel environment pre channels body =>
    cases body
    dsimp only at frames
    subst inner
    (refine ⟨[_], rfl, ?_⟩; intro root; scope_condition)
  case block fuel environment pre channels body =>
    cases body
    dsimp only at frames
    subst inner
    (refine ⟨[_], rfl, ?_⟩; intro root; scope_condition)
  case produce fuel environment incoming expression =>
    cases expression <;> try dsimp only at frames
    all_goals first
      | (subst inner; first | (refine ⟨[], rfl, ?_⟩; intro root; scope_condition) | (refine ⟨[_], rfl, ?_⟩; intro root; scope_condition))
      | (rcases frames with ⟨_, _, _, _, rfl⟩; (refine ⟨[_], rfl, ?_⟩; intro root; scope_condition))
  case build fuel environment incoming expression =>
    rcases frames with ⟨_, _, _, rfl⟩
    cases expression <;> first | (refine ⟨[_], rfl, ?_⟩; intro root; scope_condition) | (refine ⟨[_, _], rfl, ?_⟩; intro root; scope_condition)
  case statement fuel environment statement =>
    cases statement <;> try dsimp only at frames
    all_goals first
      | (subst inner; first | (refine ⟨[], rfl, ?_⟩; intro root; scope_condition) | (refine ⟨[_], rfl, ?_⟩; intro root; scope_condition))
      | (rcases frames with ⟨_, _, rfl⟩; (refine ⟨[_], rfl, ?_⟩; intro root; scope_condition))
      | skip
    case ret expression origin =>
      cases expression <;> try dsimp only at frames
      all_goals first
        | (subst inner; first | (refine ⟨[], rfl, ?_⟩; intro root; scope_condition) | (refine ⟨[_], rfl, ?_⟩; intro root; scope_condition))
        | (rcases frames with ⟨_, _, rfl⟩; (refine ⟨[_], rfl, ?_⟩; intro root; scope_condition))

private theorem nativeScopeObjects.members {α : Type} {parent : ExitInvocation α}
    {initial before final : ExecutionState} (objects : nativeScopeObjects parent initial before final)
    (entry : Goose.Core.RootInst × Value) :
    entry ∈ final.objects ↔ entry ∈ before.objects ∧ scopeRootCondition parent initial entry.1 := by
  cases parent
  all_goals try (rw [objects]; simp [scopeRootCondition])
  case block fuel environment pre channels body =>
    cases body with
    | mk scope statements tail =>
        rw [objects]
        exact Goose.Proofs.Exit.runtime_release_scope_members environment scope initial.nextScope before entry
  case activationScope fuel environment pre body =>
    cases body with
    | mk scope statements tail =>
        rw [objects]
        exact Goose.Proofs.Exit.runtime_release_scope_members environment scope initial.nextScope before entry
  case resultScope fuel environment pre channels body =>
    cases body with
    | mk scope statements tail =>
        rw [objects]
        exact Goose.Proofs.Exit.runtime_release_scope_members environment scope initial.nextScope before entry

private theorem ExitCallSite.objects_members_prefix {config : EvalConfig} {α β : Type}
    {parent : ExitInvocation α} {child : ExitInvocation β}
    {initial prepared before final : ExecutionState} {outer inner : List ExitLexicalFrame}
    (site : ExitCallSite config parent initial child prepared) (frames : site.frames outer inner)
    (objects : nativeScopeObjects parent initial before final) :
    ∃ added, inner = added ++ outer ∧ ∀ entry,
      (entry ∈ final.objects ↔ entry ∈ before.objects ∧ scopeRootsAvoid added entry.1) := by
  obtain ⟨added, shape, condition⟩ := ExitInvocation.frames_scope_prefix frames
  refine ⟨added, shape, ?_⟩
  intro entry
  rw [condition entry.1]
  exact objects.members entry

private theorem scopeRootsAvoid.append (first second : List ExitLexicalFrame) (root : Goose.Core.RootInst) :
    scopeRootsAvoid (first ++ second) root ↔ scopeRootsAvoid first root ∧ scopeRootsAvoid second root := by
  constructor
  · intro outside
    constructor
    · intro environment scope scopeInst present
      exact outside environment scope scopeInst (List.mem_append.mpr (Or.inl present))
    · intro environment scope scopeInst present
      exact outside environment scope scopeInst (List.mem_append.mpr (Or.inr present))
  · rintro ⟨firstOutside, secondOutside⟩ environment scope scopeInst present
    rcases List.mem_append.mp present with present | present
    · exact firstOutside environment scope scopeInst present
    · exact secondOutside environment scope scopeInst present

private theorem caught_handler_nearest {rootFuel fuel : Nat} {config : EvalConfig}
    {context : List ExitLexicalFrame} {environment activation handler : RuntimeActivation}
    {statement : Stmt} {initial : ExecutionState} {targetId : Nat} {address : ExitAddress}
    {discarded outer : List ExitLexicalFrame} {resultTypes : List Ty} {origin : Goose.Core.OriginId}
    (reached : ExitContextReached rootFuel config context (.statement fuel environment statement) initial)
    (selected : targetActivation config targetId initial = .ok activation initial)
    (emitted : address.activation = activation.act)
    (shape : context = discarded ++ .handler handler resultTypes origin :: outer)
    (matched : address.activation = handler.act) :
    ∃ target, config.module.targets[targetId]? = some target ∧
      target.contains handler.implementation = true ∧
      ∀ earlier ∈ discarded,
        earlier.projectedHandler.any (fun candidate => target.contains candidate.implementation) = false := by
  obtain ⟨target, nearest, nearestTypes, nearestOrigin, nearestDiscarded, nearestOuter,
    unchanged, declared, nearestShape, same, included, excluded⟩ :=
    reached.selected_handler targetId activation initial selected
  have memberOfShape : ∀ current types currentOrigin left right,
      context = left ++ .handler current types currentOrigin :: right →
      ownershipActivationChannels current ∈ context.filterMap ExitLexicalFrame.projectedHandler := by
    intro current types currentOrigin left right shaped
    apply List.mem_filterMap.mpr
    refine ⟨.handler current types currentOrigin, ?_, rfl⟩
    rw [shaped]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have nearestId : nearest.act = activation.act := congrArg (fun current : OwnershipActivationChannels => current.act) same
  have sameId : handler.act = nearest.act := matched.symm.trans (emitted.trans nearestId.symm)
  have sameChannels := handler_act_unique _ reached.handler_ids
    (ownershipActivationChannels handler) (ownershipActivationChannels nearest)
    (memberOfShape _ _ _ _ _ shape) (memberOfShape _ _ _ _ _ nearestShape) sameId
  have sameImplementation : handler.implementation = nearest.implementation :=
    congrArg (fun current : OwnershipActivationChannels => current.implementation) sameChannels
  refine ⟨target, declared, ?_, ?_⟩
  · rw [sameImplementation]
    exact included
  · have first : context.find? (fun frame => frame.projectedHandler.any
        (fun candidate => target.contains candidate.implementation)) =
        some (.handler nearest nearestTypes nearestOrigin) := by
      apply List.find?_eq_some_iff_append.mpr
      refine ⟨?_, nearestDiscarded, nearestOuter, nearestShape, ?_⟩
      · exact included
      · intro earlier present
        simp only [excluded earlier present, Bool.not_false]
    have distinct := reached.handler_ids
    rw [shape] at distinct
    have apart := lexical_handler_prefix_distinct discarded outer handler resultTypes origin distinct
    cases found : discarded.find? (fun frame => frame.projectedHandler.any
        (fun candidate => target.contains candidate.implementation)) with
    | none =>
        intro earlier present
        simpa using (List.find?_eq_none.mp found) earlier present
    | some earlier =>
        have present := List.mem_of_find?_eq_some found
        rw [shape, List.find?_append, found] at first
        have sameFrame := Option.some.inj first
        have projected : earlier.projectedHandler = some (ownershipActivationChannels nearest) := by
          rw [sameFrame]
          rfl
        exact False.elim (apart earlier present _ projected sameId.symm)

private def reachedCatch (rootFuel : Nat) (config : EvalConfig) (context : List ExitLexicalFrame)
    (address : ExitAddress) (carriers : List Carrier) (source : ExecutionState) : Prop :=
  ∃ fuel activation pre body origin enteredState before final outer discarded resultTypes,
    ExitContextReached rootFuel config outer (.activation (fuel + 1) activation pre body origin) enteredState ∧
    context = discarded ++ .handler activation resultTypes origin :: outer ∧
    address.activation = activation.act ∧
    execActivationBody fuel config activation pre body enteredState = .escape address carriers before ∧
    enterActivation (fuel + 1) config activation pre body origin enteredState = .ok carriers final ∧
    before.construction.stdout = source.construction.stdout ∧ final.construction.stdout = source.construction.stdout ∧
    (∀ root, scopeRootsAvoid discarded root → final.objects.lookup root = source.objects.lookup root) ∧
    ∀ entry, entry ∈ final.objects ↔ entry ∈ source.objects ∧ scopeRootsAvoid discarded entry.1

private theorem reachedCatch.extend {rootFuel : Nat} {config : EvalConfig} {α β : Type}
    {parent : ExitInvocation α} {child : ExitInvocation β} {initial prepared : ExecutionState}
    {outer inner : List ExitLexicalFrame} {address : ExitAddress} {carriers : List Carrier}
    {parentBefore childBefore : ExecutionState}
    (site : ExitCallSite config parent initial child prepared) (frames : site.frames outer inner)
    (caught : reachedCatch rootFuel config outer address carriers parentBefore)
    (stdout : parentBefore.construction.stdout = childBefore.construction.stdout)
    (objects : nativeScopeObjects parent initial childBefore parentBefore) :
    reachedCatch rootFuel config inner address carriers childBefore := by
  obtain ⟨fuel, activation, pre, body, origin, enteredState, before, final, context, discarded, resultTypes,
    reached, shape, matched, escaped, evaluated, beforeStdout, afterStdout, preserved, members⟩ := caught
  obtain ⟨added, extension, stepMembers⟩ := site.objects_members_prefix frames objects
  refine ⟨fuel, activation, pre, body, origin, enteredState, before, final, context, added ++ discarded, resultTypes,
    reached, ?_, matched, escaped, evaluated, beforeStdout.trans stdout, afterStdout.trans stdout, ?_, ?_⟩
  · rw [extension, shape, List.append_assoc]
  · intro root outside
    have oldOutside : scopeRootsAvoid discarded root := by
      intro environment scope scopeInst present
      exact outside environment scope scopeInst (List.mem_append.mpr (Or.inr present))
    have addedOutside : scopeRootsAvoid added root := by
      intro environment scope scopeInst present
      exact outside environment scope scopeInst (List.mem_append.mpr (Or.inl present))
    exact (preserved root oldOutside).trans
      (site.scope_objects_added frames extension objects root addedOutside)

  · intro entry
    rw [members entry, stepMembers entry, scopeRootsAvoid.append]
    exact and_assoc

private def rootUnwindStop (rootFuel : Nat) (config : EvalConfig)
    (context : List ExitLexicalFrame) (source : ExecutionState) : Prop :=
  ∃ reason final discarded outer, context = discarded ++ outer ∧
    runModule rootFuel config .initial = .stop reason final ∧
    final.construction.stdout = source.construction.stdout ∧
    (∀ root, scopeRootsAvoid discarded root → final.objects.lookup root = source.objects.lookup root) ∧
    ∀ entry, entry ∈ final.objects ↔ entry ∈ source.objects ∧ scopeRootsAvoid discarded entry.1

private theorem rootUnwindStop.extend {rootFuel : Nat} {config : EvalConfig} {α β : Type}
    {parent : ExitInvocation α} {child : ExitInvocation β} {initial prepared : ExecutionState}
    {outer inner : List ExitLexicalFrame} {parentBefore childBefore : ExecutionState}
    (site : ExitCallSite config parent initial child prepared) (frames : site.frames outer inner)
    (stopped : rootUnwindStop rootFuel config outer parentBefore)
    (stdout : parentBefore.construction.stdout = childBefore.construction.stdout)
    (objects : nativeScopeObjects parent initial childBefore parentBefore) :
    rootUnwindStop rootFuel config inner childBefore := by
  obtain ⟨reason, final, discarded, context, shape, evaluated, finalStdout, preserved, members⟩ := stopped
  obtain ⟨added, extension, stepMembers⟩ := site.objects_members_prefix frames objects
  refine ⟨reason, final, added ++ discarded, context, ?_, evaluated, finalStdout.trans stdout, ?_, ?_⟩
  · rw [extension, shape, List.append_assoc]
  · intro root outside
    obtain ⟨addedOutside, oldOutside⟩ := (scopeRootsAvoid.append added discarded root).mp outside
    exact (preserved root oldOutside).trans
      (site.scope_objects_added frames extension objects root addedOutside)
  · intro entry
    rw [members entry, stepMembers entry, scopeRootsAvoid.append]
    exact and_assoc

#print axioms rootUnwindStop.extend

#print axioms reachedCatch.extend

#print axioms ExitCallSite.escape_after_child


private theorem reachedCatch.after_delivery {rootFuel : Nat} {config : EvalConfig}
    {context : List ExitLexicalFrame} {address : ExitAddress} {carriers : List Carrier}
    {source before : ExecutionState}
    (caught : reachedCatch rootFuel config context address carriers source)
    (stdout : source.construction.stdout = before.construction.stdout) (objects : source.objects = before.objects) :
    reachedCatch rootFuel config context address carriers before := by
  obtain ⟨fuel, activation, pre, body, origin, enteredState, escapedBefore, final, outer, discarded, types,
    reached, shape, matched, escaped, returned, escapedStdout, finalStdout, preserved, members⟩ := caught
  refine ⟨fuel, activation, pre, body, origin, enteredState, escapedBefore, final, outer, discarded, types,
    reached, shape, matched, escaped, returned, escapedStdout.trans stdout, finalStdout.trans stdout, ?_, ?_⟩
  · intro root outside
    exact (preserved root outside).trans (congrArg (fun entries => entries.lookup root) objects)
  · intro entry
    rw [members entry, objects]

private theorem rootUnwindStop.after_delivery {rootFuel : Nat} {config : EvalConfig}
    {context : List ExitLexicalFrame} {source before : ExecutionState}
    (stopped : rootUnwindStop rootFuel config context source)
    (stdout : source.construction.stdout = before.construction.stdout) (objects : source.objects = before.objects) :
    rootUnwindStop rootFuel config context before := by
  obtain ⟨reason, final, discarded, outer, shape, returned, finalStdout, preserved, members⟩ := stopped
  refine ⟨reason, final, discarded, outer, shape, returned, finalStdout.trans stdout, ?_, ?_⟩
  · intro root outside
    exact (preserved root outside).trans (congrArg (fun entries => entries.lookup root) objects)
  · intro entry
    rw [members entry, objects]

private def nearestReturnCatch (rootFuel : Nat) (config : EvalConfig) (context : List ExitLexicalFrame)
    (activation : RuntimeActivation) (targetId : Nat) (carriers : List Carrier) (source : ExecutionState) : Prop :=
  ∃ target fuel handler pre body origin enteredState before final outer discarded resultTypes,
    config.module.targets[targetId]? = some target ∧
    ExitContextReached rootFuel config outer (.activation (fuel + 1) handler pre body origin) enteredState ∧
    context = discarded ++ .handler handler resultTypes origin :: outer ∧
    handler.act = activation.act ∧ target.contains handler.implementation = true ∧
    (∀ earlier ∈ discarded,
      earlier.projectedHandler.any (fun candidate => target.contains candidate.implementation) = false) ∧
    execActivationBody fuel config handler pre body enteredState =
      .escape ⟨activation.act, .nonlocal targetId⟩ carriers before ∧
    enterActivation (fuel + 1) config handler pre body origin enteredState = .ok carriers final ∧
    before.construction.stdout = source.construction.stdout ∧ final.construction.stdout = source.construction.stdout ∧
    (∀ root, scopeRootsAvoid discarded root → final.objects.lookup root = source.objects.lookup root) ∧
    ∀ entry, entry ∈ final.objects ↔ entry ∈ source.objects ∧ scopeRootsAvoid discarded entry.1

private theorem reachedCatch.nearest_return {rootFuel fuel : Nat} {config : EvalConfig}
    {context : List ExitLexicalFrame} {environment activation : RuntimeActivation} {statement : Stmt}
    {initial before : ExecutionState} {targetId : Nat} {carriers : List Carrier}
    (caught : reachedCatch rootFuel config context ⟨activation.act, .nonlocal targetId⟩ carriers before)
    (reached : ExitContextReached rootFuel config context (.statement fuel environment statement) initial)
    (selected : targetActivation config targetId initial = .ok activation initial) :
    nearestReturnCatch rootFuel config context activation targetId carriers before := by
  obtain ⟨enteredFuel, handler, pre, body, origin, enteredState, escapedBefore, final, outer, discarded, types,
    entered, shape, matched, escaped, returned, escapedStdout, finalStdout, preserved, members⟩ := caught
  obtain ⟨target, declared, included, excluded⟩ := caught_handler_nearest reached selected rfl shape matched
  exact ⟨target, enteredFuel, handler, pre, body, origin, enteredState, escapedBefore, final, outer, discarded, types,
    declared, entered, shape, matched.symm, included, excluded, escaped, returned,
    escapedStdout, finalStdout, preserved, members⟩

private theorem ExitContextReached.unwind_nonlocal {rootFuel : Nat} {config : EvalConfig}
    {context : List ExitLexicalFrame} {α : Type} {invocation : ExitInvocation α}
    {initial before : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    (reached : ExitContextReached rootFuel config context invocation initial)
    (nonlocal : address.target ≠ .ordinary)
    (escaped : invocation.action config initial = .escape address carriers before) :
    rootUnwindStop rootFuel config context before ∨
    reachedCatch rootFuel config context address carriers before := by
  induction reached generalizing before with
  | initial =>
      cases address with
      | mk activation target =>
          cases target with
          | ordinary => exact False.elim (nonlocal rfl)
          | nonlocal target =>
              exact False.elim (runModule_no_unhandled_nonlocal rootFuel config activation target carriers before escaped)
  | @call α β caller callee initial middle outer inner callerReached site frames previous =>
      rcases site.escape_after_child escaped with ⟨parentFinal, parentEscape, stdout, objects⟩ |
          ⟨reason, parentFinal, parentStop, stdout, objects⟩ | ⟨final, caught⟩
      · rcases previous parentEscape with stopped | caught
        · exact Or.inl (stopped.extend site frames stdout objects)
        · exact Or.inr (caught.extend site frames stdout objects)
      · obtain ⟨rootReason, rootFinal, changes, stopped, rootStdout, rootObjects, storage⟩ :=
          callerReached.stop_root parentStop
        have sameObjects := rootObjects.trans objects
        refine Or.inl ⟨rootReason, rootFinal, [], inner, rfl, stopped, rootStdout.trans stdout, ?_, ?_⟩
        · intro root _
          exact congrArg (fun entries => entries.lookup root) sameObjects
        · intro entry
          rw [sameObjects]
          simp [scopeRootsAvoid]
      · cases caller
        all_goals simp only [nativeHandlerCatch] at caught
        all_goals try cases caught
        case activation fuel activation pre body origin =>
          cases fuel with
          | zero => cases caught
          | succ fuel =>
              obtain ⟨matched, evaluated, returned, stdout, objects⟩ := caught
              change ∃ implementation, config.module.impls[activation.implementation]? = some implementation ∧
                inner = .handler activation (implementation.results.toList.map (fun result : ResultDescriptor => result.ty)) origin :: outer at frames
              obtain ⟨implementation, lookup, shape⟩ := frames
              exact Or.inr ⟨fuel, activation, pre, body, origin, initial, before, final, outer,
                [], implementation.results.toList.map (fun result : ResultDescriptor => result.ty), callerReached, shape, matched,
                evaluated, returned, rfl, stdout,
                (fun root _ => congrArg (fun entries => entries.lookup root) objects), by
                  intro entry
                  rw [objects]
                  simp [scopeRootsAvoid]⟩

#print axioms ExitContextReached.unwind_nonlocal

private theorem ExitContextReached.nonlocal_escape_caught_or_stopped {rootFuel : Nat} {config : EvalConfig}
    {context : List ExitLexicalFrame} {α : Type} {invocation : ExitInvocation α}
    {initial before : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    (reached : ExitContextReached rootFuel config context invocation initial)
    (nonlocal : address.target ≠ .ordinary)
    (escaped : invocation.action config initial = .escape address carriers before) :
    (∃ reason final discarded outer, context = discarded ++ outer ∧
      runModule rootFuel config .initial = .stop reason final ∧
      final.construction.stdout = before.construction.stdout ∧
      (∀ root, (∀ environment scope scopeInst,
        ExitLexicalFrame.scope environment scope scopeInst ∈ discarded →
        (Goose.Proofs.Exit.runtimeScopeRoots environment scope scopeInst).contains root = false) →
        final.objects.lookup root = before.objects.lookup root) ∧
      ∀ entry, entry ∈ final.objects ↔ entry ∈ before.objects ∧
        ∀ environment scope scopeInst,
          ExitLexicalFrame.scope environment scope scopeInst ∈ discarded →
          (Goose.Proofs.Exit.runtimeScopeRoots environment scope scopeInst).contains entry.1 = false) ∨
    ∃ fuel activation pre body origin enteredState caughtBefore final outer discarded resultTypes,
      ExitContextReached rootFuel config outer (.activation (fuel + 1) activation pre body origin) enteredState ∧
      context = discarded ++ .handler activation resultTypes origin :: outer ∧
      address.activation = activation.act ∧
      execActivationBody fuel config activation pre body enteredState = .escape address carriers caughtBefore ∧
      enterActivation (fuel + 1) config activation pre body origin enteredState = .ok carriers final ∧
      caughtBefore.construction.stdout = before.construction.stdout ∧
      final.construction.stdout = before.construction.stdout ∧
      (∀ root, (∀ environment scope scopeInst,
        ExitLexicalFrame.scope environment scope scopeInst ∈ discarded →
        (Goose.Proofs.Exit.runtimeScopeRoots environment scope scopeInst).contains root = false) →
        final.objects.lookup root = before.objects.lookup root) ∧
      ∀ entry, entry ∈ final.objects ↔ entry ∈ before.objects ∧
        ∀ environment scope scopeInst,
          ExitLexicalFrame.scope environment scope scopeInst ∈ discarded →
          (Goose.Proofs.Exit.runtimeScopeRoots environment scope scopeInst).contains entry.1 = false :=
  reached.unwind_nonlocal nonlocal escaped

#print axioms ExitContextReached.nonlocal_escape_caught_or_stopped

private theorem ExitContextReached.returnFrom_after_operands_unwind {rootFuel fuel : Nat} {config : EvalConfig}
    {context : List ExitLexicalFrame} {environment activation : RuntimeActivation} {targetId : Nat}
    {operands : List Expr} {origin : Goose.Core.OriginId} {initial prepared before : ExecutionState}
    {channels : List Channel} {raw : List Carrier}
    (reached : ExitContextReached rootFuel config context
      (.statement (fuel + 1) environment (.returnFrom targetId operands origin)) initial)
    (selected : targetActivation config targetId initial = .ok activation initial)
    (setup : exitChannels environment activation operands origin initial = .ok channels prepared)
    (evaluated : evalOperands fuel config environment channels operands prepared = .ok raw before) :
    rootUnwindStop rootFuel config context before ∨
      ∃ carriers, nearestReturnCatch rootFuel config context activation targetId carriers before := by
  rcases withExitChannels_ok_after_action environment activation operands origin
    (fun outputs => evalOperands fuel config environment outputs operands)
    initial prepared before channels raw setup evaluated with
      ⟨carriers, final, changes, returned, stdout, objects, storage⟩ |
      ⟨reason, final, changes, returned, stdout, objects, storage⟩
  · have escaped : execStmt (fuel + 1) config environment (.returnFrom targetId operands origin) initial =
        .escape ⟨activation.act, .nonlocal targetId⟩ carriers final := by
      simp only [execStmt, bind, selected, returned, Goose.Construct.escaped]
    rcases reached.unwind_nonlocal (by intro impossible; cases impossible) escaped with stopped | caught
    · exact Or.inl (stopped.after_delivery stdout objects)
    · exact Or.inr ⟨carriers, (caught.after_delivery stdout objects).nearest_return reached selected⟩
  · have stopped : execStmt (fuel + 1) config environment (.returnFrom targetId operands origin) initial =
        .stop reason final := by
      simp only [execStmt, bind, selected, returned]
    obtain ⟨rootReason, rootFinal, rootChanges, rootStopped, rootStdout, rootObjects, rootStorage⟩ :=
      reached.stop_root stopped
    have sameObjects := rootObjects.trans objects
    refine Or.inl ⟨rootReason, rootFinal, [], context, rfl, rootStopped, rootStdout.trans stdout, ?_, ?_⟩
    · intro root _
      exact congrArg (fun entries => entries.lookup root) sameObjects
    · intro entry
      rw [sameObjects]
      simp [scopeRootsAvoid]

#print axioms ExitContextReached.returnFrom_after_operands_unwind

private theorem ExitContextReached.returnFromForward_after_operands_unwind {rootFuel fuel : Nat} {config : EvalConfig}
    {context : List ExitLexicalFrame} {environment activation : RuntimeActivation} {targetId : Nat}
    {producer : Expr} {origin : Goose.Core.OriginId} {initial prepared before : ExecutionState}
    {channels : List Channel} {raw : List Carrier}
    (reached : ExitContextReached rootFuel config context
      (.statement (fuel + 1) environment (.returnFromForward targetId producer origin)) initial)
    (selected : targetActivation config targetId initial = .ok activation initial)
    (setup : exitChannels environment activation (List.replicate activation.channels.length producer) origin initial = .ok channels prepared)
    (evaluated : evalProduce fuel config environment channels producer prepared = .ok raw before) :
    rootUnwindStop rootFuel config context before ∨
      ∃ carriers, nearestReturnCatch rootFuel config context activation targetId carriers before := by
  rcases withExitChannels_ok_after_action environment activation (List.replicate activation.channels.length producer) origin
    (fun outputs => evalProduce fuel config environment outputs producer)
    initial prepared before channels raw setup evaluated with
      ⟨carriers, final, changes, returned, stdout, objects, storage⟩ |
      ⟨reason, final, changes, returned, stdout, objects, storage⟩
  · have escaped : execStmt (fuel + 1) config environment (.returnFromForward targetId producer origin) initial =
        .escape ⟨activation.act, .nonlocal targetId⟩ carriers final := by
      simp only [execStmt, bind, selected, returned, Goose.Construct.escaped]
    rcases reached.unwind_nonlocal (by intro impossible; cases impossible) escaped with stopped | caught
    · exact Or.inl (stopped.after_delivery stdout objects)
    · exact Or.inr ⟨carriers, (caught.after_delivery stdout objects).nearest_return reached selected⟩
  · have stopped : execStmt (fuel + 1) config environment (.returnFromForward targetId producer origin) initial =
        .stop reason final := by
      simp only [execStmt, bind, selected, returned]
    obtain ⟨rootReason, rootFinal, rootChanges, rootStopped, rootStdout, rootObjects, rootStorage⟩ :=
      reached.stop_root stopped
    have sameObjects := rootObjects.trans objects
    refine Or.inl ⟨rootReason, rootFinal, [], context, rfl, rootStopped, rootStdout.trans stdout, ?_, ?_⟩
    · intro root _
      exact congrArg (fun entries => entries.lookup root) sameObjects
    · intro entry
      rw [sameObjects]
      simp [scopeRootsAvoid]

#print axioms ExitContextReached.returnFromForward_after_operands_unwind

end Goose.Proofs.ExitExecution
