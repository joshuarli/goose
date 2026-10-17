import Goose.Lower.Validation.ReplacementSourceSitesOutputs
import Goose.Lower.Validation.ReplacementSourceSitesWhole
import Goose.Lower.Validation.ReplacementSourceSitesResize
import Goose.Lower.Validation.ReplacementSourceSitesRebind
import Goose.Lower.Validation.ReplacementSourceSitesTransfers
import Goose.Lower.Validation.ReplacementSourceSitesShortCircuit
import Goose.Lower.Validation.ReplacementSourceSitesBlocks
import Goose.Lower.Validation.ReplacementSourceSitesEach
import Goose.Lower.Validation.ReplacementSourceSitesEachValue
import Goose.Lower.Validation.OperandEach
import Goose.Lower.Validation.ReplacementSourceSitesSliceReference
import Goose.Lower.Validation.SourceStatementTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {root : DemandNode}

attribute [local irreducible] ReplacementSitesAt

set_option maxHeartbeats 1600000 in
mutual

theorem replacementSites_lowerExpr {targets : List BlockId} (expr : Expr) {env : Core.TEnv} (sourceTypes : SourceReadableEnvironment env)
    {type : Ty} {start finish : Nat} (source : Core.tyExpr env expr start = .ok (type, finish))
    (results : List Ty) {before : LS} (generated : GeneratedBuilderState before)
    (location : ReplacementDemandLocation root (.expression expr)) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerExpr expr) := by
  cases expr with
  | lit type value | bool value => exact ReplacementSitesAt.emitDef _ (by intros; trivial)
  | read place =>
    apply replacementSites_read_source source
    · intro info first last childSource state current
      exact replacementSites_lowerPlace (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) place sourceTypes childSource results current
    · exact generated
  | push owner value origin =>
    apply replacementSites_push_source source
    · intro info first last childSource state current
      exact replacementSites_lowerPlace (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) owner sourceTypes childSource results current
    · intro childType first last childSource state current
      exact replacementSites_lowerExpr (location := (location.child 1 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) value sourceTypes childSource results current
    · exact generated
  | pop owner origin =>
    apply replacementSites_pop_source source
    · intro info first last childSource state current
      exact replacementSites_lowerPlace (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) owner sourceTypes childSource results current
    · exact generated
  | ref mutability place =>
    obtain ⟨info, next, placeSource, _, _⟩ := tyExpr_ref_place source
    exact (replacementSites_lowerPlace (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) place sourceTypes placeSource results generated).bind (ReplacementSitesAt.borrowTo _ _ _ _)
  | len view =>
    simp only [Core.tyExpr] at source
    obtain ⟨pair, next, childSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact (replacementSites_lowerView (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) view sourceTypes childSource results generated).bind (ReplacementSitesAt.emitDef _ (by intros; trivial))
  | un operation child origin =>
    obtain ⟨first, last, integer, childSource, _, _⟩ := tyExpr_un_child source
    exact (replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) child sourceTypes childSource results generated).bind
      ((ReplacementSitesAt.intTyOf _ _ _).bind (ReplacementSitesAt.emitDef _ (by intros; trivial)))
  | not child =>
    obtain ⟨next, childSource, _⟩ := tyExpr_not_child source
    exact (replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) child sourceTypes childSource results generated).bind (ReplacementSitesAt.emitDef _ (by intros; trivial))
  | bin operation left right origin =>
    obtain ⟨leftStart, leftFinish, rightStart, rightFinish, integer, leftSource, rightSource, _⟩ := tyExpr_bin_children source
    apply (replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) left sourceTypes leftSource results generated).bind
    apply (replacementSites_lowerExpr (location := (location.child 1 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) right sourceTypes rightSource results
      (generated.lowerExpr left (env := lowerEnv env.mod env.vars results) rfl)).bind
    exact (ReplacementSitesAt.intTyOf _ _ _).bind (ReplacementSitesAt.emitDef _ (by intros; trivial))
  | cmp operation left right =>
    obtain ⟨leftType, rightType, leftFinish, rightFinish, leftSource, rightSource, _, _⟩ := tyExpr_comparison_children source
    apply (replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) left sourceTypes leftSource results generated).bind
    apply (replacementSites_lowerExpr (location := (location.child 1 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) right sourceTypes rightSource results
      (generated.lowerExpr left (env := lowerEnv env.mod env.vars results) rfl)).bind
    apply (ReplacementSitesAt.valTy _ _ _).bind
    split <;> exact ReplacementSitesAt.emitDef _ (by intros; trivial)
  | conv kind target child origin =>
    obtain ⟨src, dst, childStart, childFinish, childSource, _, _, _⟩ := tyExpr_conversion_child source
    apply (replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) child sourceTypes childSource results generated).bind
    exact (ReplacementSitesAt.intTyOf _ _ _).bind (ReplacementSitesAt.emitDef _ (by intros; trivial))
  | and left right | or left right =>
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, leftSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, rightSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    apply (replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) left sourceTypes leftSource results generated).bind
    apply ReplacementSitesAt.shortCircuit_generated _ _ (generated.lowerExpr left (env := lowerEnv env.mod env.vars results) rfl)
    intro state current
    exact replacementSites_lowerExpr (location := (location.child 1 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) right sourceTypes rightSource results current
  | slice mutability view lower upper origin =>
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨pair, _, viewSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, lowerSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, upperSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    apply (replacementSites_lowerView (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) view sourceTypes viewSource results generated).bind
    have viewGenerated := generated.lowerView view (env := lowerEnv env.mod env.vars results) rfl
    apply (replacementSites_lowerBound (location := (location.child 1 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) lower sourceTypes lowerSource results viewGenerated).bind
    apply (replacementSites_lowerBound (location := (location.child 2 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) upper sourceTypes upperSource results
      (viewGenerated.lowerBound lower (env := lowerEnv env.mod env.vars results) rfl)).bind
    exact ReplacementSitesAt.emitDef _ (by intros; trivial)
  | arrLit arrayType children =>
    obtain ⟨_, element, childStart, childFinish, _, _, childrenSource⟩ := tyExpr_arrayLiteral_children source
    exact (replacementSites_lowerExprsAs (locations := (location.expressionChildren children rfl)) (targets := _) children sourceTypes childrenSource results generated).bind
      (ReplacementSitesAt.emitDef _ (by intros; trivial))
  | structLit structType children =>
    obtain ⟨_, descriptor, definitionFinish, childStart, childFinish, _, childrenSource⟩ := tyExpr_structLiteral_children source
    exact (replacementSites_lowerStructExprs (locations := (location.expressionChildren children rfl)) (targets := _) children sourceTypes childrenSource results generated).bind
      (ReplacementSitesAt.emitDef _ (by intros; trivial))
  | fill arrayType child =>
    obtain ⟨_, element, size, childStart, childFinish, _, childSource⟩ := tyExpr_fill_child source
    exact (replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) child sourceTypes childSource results generated).bind (ReplacementSitesAt.emitDef _ (by intros; trivial))
  | call context arguments origin =>
    obtain ⟨ctx, callee, argsStart, argsFinish, resultStart, _, _, length, argsSource, _⟩ := tyExpr_call_tables source
    apply (replacementSites_lowerArgs (locations := location.arguments) (targets := _) arguments callee.params.toList sourceTypes argsSource length results generated).bind
    apply (ReplacementSitesAt.emitDef _ (by intros; trivial)).bind
    apply (ReplacementSitesAt.read _ _).bind
    split
    · exact (ReplacementSitesAt.emitTerm _ _ _).bind (ReplacementSitesAt.pure _ _ _)
    · exact (ReplacementSitesAt.pure _ _ _).bind (ReplacementSitesAt.pure _ _ _)
  | blockE body =>
    exact replacementSites_lowerBlock (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) body sourceTypes.exprEnv source results none [] true generated trivial (by simp [ReplacementLoopTargetsIncluded, LoopBuilderFrameTargets])
  | ifE condition thenBody elseBody =>
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, conditionSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, thenSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, elseSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    apply (replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) condition sourceTypes conditionSource results generated).bind
    apply ReplacementSitesAt.whenLive
    intro current live
    apply ReplacementSitesAt.fork_actions_generated _
      (generated.lowerExpr condition (env := lowerEnv env.mod env.vars results) rfl) (loop := none) trivial
      (dense_lowerBlock none [] true thenBody) (generatedTargets_lowerBlock none [] true thenBody)
    · intro state current bounds
      exact replacementSites_lowerBlock (location := (location.child 1 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) thenBody sourceTypes.exprEnv thenSource results none [] true current trivial (by simp [ReplacementLoopTargetsIncluded, LoopBuilderFrameTargets])
    · intro state current bounds
      exact replacementSites_lowerBlock (location := (location.child 2 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) elseBody sourceTypes.exprEnv elseSource results none [] true current trivial (by simp [ReplacementLoopTargetsIncluded, LoopBuilderFrameTargets])
    · intro endT valueT endF valueF state
      change ReplacementSitesAt (root := root) (targets := _) _ state
        (joinValue endT valueT endF valueF >>= fun result => do
          recordValueRootRecipe result (sourceBlockScope thenBody)
          pure result)
      apply ReplacementSitesAt.bind
      · exact ReplacementSitesAt.joinValue _ state endT valueT endF valueF
      · apply (ReplacementSitesFree.recordValueRootRecipe _ _ _ _).at.bind
        exact ReplacementSitesAt.pure _ _ _
termination_by sizeOf expr

theorem replacementSites_lowerPlace {targets : List BlockId} (place : Place) {env : Core.TEnv} (sourceTypes : SourceReadableEnvironment env)
    {info : PlaceInfo} {start finish : Nat} (source : Core.tyPlace env place start = .ok (info, finish))
    (results : List Ty) {before : LS} (generated : GeneratedBuilderState before)
    (location : ReplacementDemandLocation root (.place place)) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerPlace place) := by
  cases place with
  | var slot | global slot => exact ReplacementSitesAt.emitDef _ (by intros; trivial)
  | field owner index =>
    simp only [Core.tyPlace] at source
    obtain ⟨_, _, ownerSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact (replacementSites_lowerPlace (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) owner sourceTypes ownerSource results generated).bind (ReplacementSitesAt.emitDef _ (by intros; trivial))
  | elem view index origin =>
    simp only [Core.tyPlace] at source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, viewSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, indexSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    apply (replacementSites_lowerView (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) view sourceTypes viewSource results generated).bind
    apply (replacementSites_lowerExpr (location := (location.child 1 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) index sourceTypes indexSource results
      (generated.lowerView view (env := lowerEnv env.mod env.vars results) rfl)).bind
    exact ReplacementSitesAt.emitDef _ (by intros; trivial)
  | deref expr =>
    simp only [Core.tyPlace] at source
    obtain ⟨_, _, valueSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    cases shortcut : Core.sliceRefTy env expr with
    | some type => exact replacementSites_sliceRef_source shortcut generated
    | none =>
      simp only [shortcut] at valueSource
      obtain ⟨_, _, childSource, _⟩ := (st_bind_ok _ _ _ _).mp valueSource
      exact replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) expr sourceTypes childSource results generated
termination_by sizeOf place

theorem replacementSites_lowerView {targets : List BlockId} (view : View) {env : Core.TEnv} (sourceTypes : SourceReadableEnvironment env)
    {pair : Ty × Bool} {start finish : Nat} (source : Core.tyView env view start = .ok (pair, finish))
    (results : List Ty) {before : LS} (generated : GeneratedBuilderState before)
    (location : ReplacementDemandLocation root (.view view)) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerView view) := by
  cases view with
  | of place =>
    simp only [Core.tyView] at source
    obtain ⟨_, _, placeSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact (replacementSites_lowerPlace (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) place sourceTypes placeSource results generated).bind (ReplacementSitesAt.emitDef _ (by intros; trivial))
  | val expr =>
    simp only [Core.tyView] at source
    obtain ⟨_, _, childSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact (replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) expr sourceTypes childSource results generated).bind (ReplacementSitesAt.emitDef _ (by intros; trivial))
termination_by sizeOf view

theorem replacementSites_lowerBound {targets : List BlockId} (bound : Bound) {env : Core.TEnv} (sourceTypes : SourceReadableEnvironment env)
    {start finish : Nat} (source : Core.tyBound env bound start = .ok ((), finish))
    (results : List Ty) {before : LS} (generated : GeneratedBuilderState before)
    (location : ReplacementDemandLocation root (.bound bound)) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerBound bound) := by
  cases bound with
  | omitted => exact ReplacementSitesAt.pure _ _ _
  | expr child | fromEnd child =>
    simp only [Core.tyBound] at source
    obtain ⟨_, _, childSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact (replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) child sourceTypes childSource results generated).bind (ReplacementSitesAt.pure _ _ _)
termination_by sizeOf bound

theorem replacementSites_lowerExprsAs {targets : List BlockId} (expressions : List Expr) {env : Core.TEnv}
    (sourceTypes : SourceReadableEnvironment env) {element : Ty} {start finish : Nat}
    (source : Core.tyExprsAs env element expressions start = .ok ((), finish))
    (results : List Ty) {before : LS} (generated : GeneratedBuilderState before)
    (locations : ReplacementDemandLocations root DemandNode.expression expressions) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerExprs expressions) := by
  cases expressions with
  | nil => exact ReplacementSitesAt.pure _ _ _
  | cons expression rest =>
    simp only [Core.tyExprsAs] at source
    obtain ⟨type, next, childSource, tail⟩ := (st_bind_ok _ _ _ _).mp source
    have tailSource : Core.tyExprsAs env element rest next = .ok ((), finish) := by
      by_cases equal : (type == element) = true
      · simpa [equal, pure, bind, StateT.pure, StateT.bind] using tail
      · simp [equal, chk] at tail
    apply (replacementSites_lowerExpr (location := locations.head) (targets := _) expression sourceTypes childSource results generated).bind
    exact (replacementSites_lowerExprsAs (locations := locations.tail) (targets := _) rest sourceTypes tailSource results
      (generated.lowerExpr expression (env := lowerEnv env.mod env.vars results) rfl)).bind (ReplacementSitesAt.pure _ _ _)
termination_by sizeOf expressions

theorem replacementSites_lowerStructExprs {targets : List BlockId} (expressions : List Expr) {env : Core.TEnv}
    (sourceTypes : SourceReadableEnvironment env) {types : List Ty} {start finish : Nat}
    (source : Core.tyStructExprs env types expressions start = .ok ((), finish))
    (results : List Ty) {before : LS} (generated : GeneratedBuilderState before)
    (locations : ReplacementDemandLocations root DemandNode.expression expressions) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerExprs expressions) := by
  cases expressions with
  | nil => exact ReplacementSitesAt.pure _ _ _
  | cons expression rest =>
    cases types with
    | nil => simp [Core.tyStructExprs, chk] at source
    | cons expected types =>
      simp only [Core.tyStructExprs] at source
      obtain ⟨type, next, childSource, tail⟩ := (st_bind_ok _ _ _ _).mp source
      have tailSource : Core.tyStructExprs env types rest next = .ok ((), finish) := by
        by_cases equal : (type == expected) = true
        · simpa [equal, pure, bind, StateT.pure, StateT.bind] using tail
        · simp [equal, chk] at tail
      apply (replacementSites_lowerExpr (location := locations.head) (targets := _) expression sourceTypes childSource results generated).bind
      exact (replacementSites_lowerStructExprs (locations := locations.tail) (targets := _) rest sourceTypes tailSource results
        (generated.lowerExpr expression (env := lowerEnv env.mod env.vars results) rfl)).bind (ReplacementSitesAt.pure _ _ _)
termination_by sizeOf expressions

theorem replacementSites_lowerArgs {targets : List BlockId} (arguments : List Arg) (parameters : List Param) {env : Core.TEnv}
    (sourceTypes : SourceReadableEnvironment env) {callee : Core.Impl} {start finish : Nat}
    (source : Core.tyArgs env callee parameters arguments start = .ok ((), finish))
    (length : parameters.length = arguments.length)
    (results : List Ty) {before : LS} (generated : GeneratedBuilderState before)
    (locations : ReplacementDemandLocations root replacementDemandArgumentNode arguments) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerArgs arguments) := by
  cases arguments with
  | nil => exact ReplacementSitesAt.pure _ _ _
  | cons argument rest =>
    cases parameters with
    | nil => simp at length
    | cons parameter parameters =>
      have tailLength : parameters.length = rest.length := by simpa using length
      cases row : callee.vars[parameter.var]? with
      | none =>
        cases argument <;> simp only [Core.tyArgs, row] at source
        all_goals inv at source
      | some localVar =>
        cases argument with
        | byVal expression =>
          simp only [Core.tyArgs, row] at source
          inv at source
          repeat' first
            | (guard_hyp source : _ ∧ _; obtain ⟨fact, source⟩ := source)
            | (guard_hyp source : ∃ _, _; obtain ⟨value, source⟩ := source)
          apply ReplacementSitesAt.bind
          · exact replacementSites_lowerExpr (location := locations.head) (targets := _) expression sourceTypes (by assumption) results generated
          · exact (replacementSites_lowerArgs (locations := locations.tail) (targets := _) rest parameters sourceTypes (by assumption) tailLength results
              (generated.lowerArg (.byVal expression) (env := lowerEnv env.mod env.vars results) rfl)).bind (ReplacementSitesAt.pure _ _ _)
        | byRef mutability place =>
          simp only [Core.tyArgs, row] at source
          inv at source
          repeat' first
            | (guard_hyp source : _ ∧ _; obtain ⟨fact, source⟩ := source)
            | (guard_hyp source : ∃ _, _; obtain ⟨value, source⟩ := source)
          have tailSource : ∃ next, Core.tyArgs env callee parameters rest next = .ok ((), finish) := by
            rcases source with ⟨_, _, _, tail⟩ | ⟨_, _, tail⟩
            all_goals exact ⟨_, tail⟩
          obtain ⟨next, tailSource⟩ := tailSource
          apply ReplacementSitesAt.bind
          · exact (replacementSites_lowerPlace (location := locations.head) (targets := _) place sourceTypes (by assumption) results generated).bind (ReplacementSitesAt.borrowTo _ _ _ _)
          · exact (replacementSites_lowerArgs (locations := locations.tail) (targets := _) rest parameters sourceTypes tailSource tailLength results
              (generated.lowerArg (.byRef mutability place) (env := lowerEnv env.mod env.vars results) rfl)).bind (ReplacementSitesAt.pure _ _ _)
termination_by sizeOf arguments

theorem replacementSites_lowerPrintArgs {targets : List BlockId} (arguments : List PrintArg) {env : Core.TEnv}
    (sourceTypes : SourceReadableEnvironment env) {start finish : Nat}
    (source : Core.tyPrintArgs env arguments start = .ok ((), finish))
    (results : List Ty) {before : LS} (generated : GeneratedBuilderState before)
    (locations : ReplacementDemandPrintLocations root arguments) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerPrintArgs arguments) := by
  cases arguments with
  | nil => exact ReplacementSitesAt.pure _ _ _
  | cons argument rest =>
    cases argument with
    | text text => exact (replacementSites_lowerPrintArgs (locations := locations.tail) (targets := _) rest sourceTypes source results generated).bind (ReplacementSitesAt.pure _ _ _)
    | expr expression =>
      simp only [Core.tyPrintArgs] at source
      obtain ⟨type, next, childSource, tail⟩ := (st_bind_ok _ _ _ _).mp source
      have tailSource : Core.tyPrintArgs env rest next = .ok ((), finish) := by
        cases type <;> simp only at tail
        all_goals first | exact tail | exact (rej_ok _ _ _ _).mp tail |>.elim
      apply (replacementSites_lowerExpr (location := (locations 0 expression rfl)) (targets := _) expression sourceTypes childSource results generated).bind
      exact (replacementSites_lowerPrintArgs (locations := locations.tail) (targets := _) rest sourceTypes tailSource results
        (generated.lowerExpr expression (env := lowerEnv env.mod env.vars results) rfl)).bind (ReplacementSitesAt.pure _ _ _)
termination_by sizeOf arguments

theorem replacementSites_lowerBlock {targets : List BlockId} (body : Core.Block) {env : Core.TEnv} (sourceTypes : SourceReadableEnvironment env)
    {sourcePre : List (VarId × Ty)} {type : Ty} {start finish : Nat}
    (source : Core.tyBlock env sourcePre body start = .ok (type, finish))
    (results : List Ty) (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool)
    {before : LS} (generated : GeneratedBuilderState before) (bounds : LoopBuilderTargets loop before)
    (allowed : ReplacementLoopTargetsIncluded loop targets)
    (location : ReplacementDemandLocation root (.block body)) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerBlock loop pre want body) := by
  cases body with
  | mk scope statements value =>
    obtain ⟨_, declared, output, statementStart, valueStart, declaration, statementsSource, valueSource⟩ := tyBlock_checked_children source
    have declaredTables := declarePre_tables sourcePre declaration
    have outputTables := tyStmts_tables statements statementsSource
    have declaredTypes := sourceTypes.tables declaredTables.1 declaredTables.2.1
    have outputTypes := declaredTypes.tables outputTables.1 outputTables.2.1
    have declaredEnv := declarePre_lowerEnv declaration results
    have outputEnv := (tyStmts_lowerEnv statementsSource results).trans declaredEnv
    apply ReplacementSitesAt.block_generated loop pre want scope statements value generated bounds
    · intro state current childBounds
      simpa only [declaredEnv] using replacementSites_lowerStmts (locations := location.statements) (targets := _) statements declaredTypes statementsSource results loop current childBounds allowed
    · intro state current
      cases value with
      | none => cases want <;> first | exact ReplacementSitesAt.pure _ _ _ | exact ReplacementSitesAt.emitDef _ (by intros; trivial)
      | some expression =>
        simpa only [outputEnv, lowerBlockValue] using replacementSites_lowerExpr (location := location.blockValue) (targets := _) expression outputTypes valueSource results current
termination_by sizeOf body

theorem replacementSites_lowerStmts {targets : List BlockId} (statements : List Stmt) {env output : Core.TEnv}
    (sourceTypes : SourceReadableEnvironment env) {scope start finish : Nat}
    (source : Core.tyStmts env scope statements start = .ok (output, finish))
    (results : List Ty) (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before)
    (bounds : LoopBuilderTargets loop before)
    (allowed : ReplacementLoopTargetsIncluded loop targets)
    (locations : ReplacementDemandLocations root DemandNode.statement statements) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerStmts loop statements) := by
  cases statements with
  | nil => exact ReplacementSitesAt.pure _ _ _
  | cons statement rest =>
    obtain ⟨middle, next, headSource, tailSource⟩ := tyStmts_cons_children source
    have tables := tyStmt_tables statement headSource
    have middleTypes := sourceTypes.tables tables.1 tables.2.1
    have middleEnv : lowerEnv middle.mod middle.vars results = lowerEnv env.mod env.vars results := by rw [tables.1, tables.2.1]
    unfold lowerStmts
    apply (ReplacementSitesAt.isLive _ _).bind
    split
    · apply (replacementSites_lowerStmt (location := locations.head) (targets := _) statement sourceTypes headSource results loop generated bounds allowed).bind
      have nextGenerated := generated.lowerStmt loop statement bounds (env := lowerEnv env.mod env.vars results) rfl
      have nextBounds := (generatedTargets_lowerStmt loop statement (lowerEnv env.mod env.vars results) before _ _ rfl generated.targets bounds).2
      simpa only [middleEnv] using replacementSites_lowerStmts (locations := locations.tail) (targets := _) rest middleTypes tailSource results loop nextGenerated nextBounds allowed
    · exact ReplacementSitesAt.pure _ _ _
termination_by sizeOf statements

theorem replacementSites_lowerStmt {targets : List BlockId} (statement : Stmt) {env output : Core.TEnv}
    (sourceTypes : SourceReadableEnvironment env) {scope start finish : Nat}
    (source : Core.tyStmt env scope statement start = .ok (output, finish))
    (results : List Ty) (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before)
    (bounds : LoopBuilderTargets loop before)
    (allowed : ReplacementLoopTargetsIncluded loop targets)
    (location : ReplacementDemandLocation root (.statement statement)) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerStmt loop statement) := by
  cases statement with
  | letS slot expr origin =>
    apply replacementSites_let_source source
    · intro type first last childSource state current
      exact replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) expr sourceTypes childSource results current
    · exact generated
  | assign place expr origin =>
    apply replacementSites_assign_source source
    · intro info first last childSource state current
      exact replacementSites_lowerPlace (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) place sourceTypes childSource results current
    · intro type first last childSource state current
      exact replacementSites_lowerExpr (location := (location.child 1 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) expr sourceTypes childSource results current
    · exact generated
  | assignOp operation place expr origin =>
    apply replacementSites_assignOp_source source
    · intro info first last childSource state current
      exact replacementSites_lowerPlace (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) place sourceTypes childSource results current
    · intro type first last childSource state current
      exact replacementSites_lowerExpr (location := (location.child 1 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) expr sourceTypes childSource results current
    · exact generated
  | rebind slot expr origin =>
    apply replacementSites_rebind_source source sourceTypes
    · intro type first last childSource state current
      exact replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) expr sourceTypes childSource results current
    · exact generated
  | expr expr origin =>
    apply replacementSites_expr_source source
    · intro type first last childSource state current
      exact replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) expr sourceTypes childSource results current
    · exact generated
  | append owner view origin =>
    apply replacementSites_append_source source
    · intro info first last childSource state current
      exact replacementSites_lowerPlace (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) owner sourceTypes childSource results current
    · intro element writable first last childSource state current
      exact replacementSites_lowerView (location := (location.child 1 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) view sourceTypes childSource results current
    · exact generated
  | popN owner count origin =>
    apply replacementSites_popN_source source
    · intro info first last childSource state current
      exact replacementSites_lowerPlace (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) owner sourceTypes childSource results current
    · intro type first last childSource state current
      exact replacementSites_lowerExpr (location := (location.child 1 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) count sourceTypes childSource results current
    · exact generated
  | resize owner size fill origin =>
    apply replacementSites_resize_source source
    · intro info first last childSource state current
      exact replacementSites_lowerPlace (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) owner sourceTypes childSource results current
    · intro type first last childSource state current
      exact replacementSites_lowerExpr (location := (location.child 1 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) size sourceTypes childSource results current
    · intro expression atFill type first last childSource state current
      cases atFill
      exact replacementSites_lowerExpr (location := (location.child 2 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) expression sourceTypes childSource results current
    · exact generated
  | clear owner origin =>
    apply replacementSites_clear_source source
    · intro info first last childSource state current
      exact replacementSites_lowerPlace (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) owner sourceTypes childSource results current
    · exact generated
  | assignWhole owner expr origin =>
    refine replacementSites_assignWhole_source source ?_ ?_ loop generated location
    · intro info first last childSource state current
      exact replacementSites_lowerPlace (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) owner sourceTypes childSource results current
    · intro type first last childSource state current
      exact replacementSites_lowerExpr (location := (location.child 1 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) expr sourceTypes childSource results current
  | ret value origin =>
    cases value with
    | none => exact ReplacementSitesAt.return_none _ _ _ _
    | some expr =>
      apply replacementSites_return_source source
      · intro type first last childSource state current
        exact replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) expr sourceTypes childSource results current
      · exact generated
  | brk origin => exact ReplacementSitesAt.breakStmt _ _ _ _ allowed
  | cont origin => exact ReplacementSitesAt.continueStmt _ _ _ _ allowed
  | abort message origin => exact ReplacementSitesAt.emitTerm _ _ _
  | exit expr origin =>
    apply replacementSites_exit_source source
    · intro type first last childSource state current
      exact replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) expr sourceTypes childSource results current
    · exact generated
  | assertS expr origin =>
    apply replacementSites_assert_source source
    · intro type first last childSource state current
      exact replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) expr sourceTypes childSource results current
    · exact generated
  | print arguments origin =>
    exact (replacementSites_lowerPrintArgs (locations := location.printArguments) (targets := _) arguments sourceTypes (tyStmt_print_children source).1 results generated).bind
      (ReplacementSitesAt.emitEffect _ (by intros; trivial))
  | ifS condition thenBody otherwise origin =>
    cases otherwise with
    | some elseBody =>
      obtain ⟨conditionFinish, thenType, thenFinish, conditionSource, thenSource, elseSource, _⟩ := tyStmt_if_children source
      let le := lowerEnv env.mod env.vars results
      let tested := lowerExpr condition le before
      have testedGenerated := generated.lowerExpr condition (show lowerExpr condition le before = tested from rfl)
      have testedBounds := bounds.mono
        ((dense_lowerExpr condition le before tested.1 tested.2 rfl generated.dense generated.live).2.2)
      apply (replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) condition sourceTypes conditionSource results generated).bind
      apply ReplacementSitesAt.whenLive
      intro current live
      obtain ⟨elseType, childSource⟩ := elseSource
      apply ReplacementSitesAt.fork_actions_generated _ testedGenerated testedBounds
        (dense_lowerBlock loop [] false thenBody) (generatedTargets_lowerBlock loop [] false thenBody)
      · intro state current childBounds
        exact replacementSites_lowerBlock (location := (location.child 1 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) thenBody sourceTypes thenSource results loop [] false current childBounds allowed
      · intro state current childBounds
        exact replacementSites_lowerBlock (location := (location.child 2 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) elseBody sourceTypes childSource results loop [] false current childBounds allowed
      · exact fun _ _ _ _ state => ReplacementSitesAt.joinArms _ state _ _
    | none =>
      obtain ⟨conditionFinish, thenType, thenFinish, conditionSource, thenSource, elseSource, _⟩ := tyStmt_if_children source
      let le := lowerEnv env.mod env.vars results
      let tested := lowerExpr condition le before
      have testedGenerated := generated.lowerExpr condition (show lowerExpr condition le before = tested from rfl)
      have testedBounds := bounds.mono
        ((dense_lowerExpr condition le before tested.1 tested.2 rfl generated.dense generated.live).2.2)
      apply (replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) condition sourceTypes conditionSource results generated).bind
      apply ReplacementSitesAt.whenLive
      intro current live
      apply ReplacementSitesAt.ifThen_generated tested.1 testedGenerated testedBounds
      intro state current childBounds
      exact replacementSites_lowerBlock (location := (location.child 1 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) thenBody sourceTypes thenSource results loop [] false current childBounds
        (fun target member => List.mem_cons_of_mem _ (allowed target member))
  | «while» condition body origin =>
    obtain ⟨conditionFinish, bodyType, conditionSource, bodySource, _⟩ := tyStmt_while_children source
    apply ReplacementSitesAt.header_generated (α := Unit)
      (tail := fun header _ => lowerWhile header (lowerExpr condition)
        (fun depth exit => lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body)) [] [] generated
    intro header parameters state current headerBound
    let le := lowerEnv env.mod env.vars results
    let tested := lowerExpr condition le state
    have testedGenerated := current.lowerExpr condition (show lowerExpr condition le state = tested from rfl)
    have headerLater : header < tested.2.blocks.size := Nat.lt_of_lt_of_le headerBound
      ((dense_lowerExpr condition le state tested.1 tested.2 rfl current.dense current.live).2.2)
    apply ReplacementSitesAt.lowerWhile_generated header (by simp)
      (replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) condition sourceTypes conditionSource results current) testedGenerated
    intro depth exit bodyState bodyGenerated exitBound grows
    exact replacementSites_lowerBlock (location := (location.child 1 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) body (sourceTypes.tables (after := { env with loops := env.loops + 1 }) rfl rfl) bodySource results
      (some ⟨depth, exit, .jump header⟩) [] false bodyGenerated
      ⟨exitBound, Nat.lt_of_lt_of_le headerLater grows⟩
      (by simp [ReplacementLoopTargetsIncluded, LoopBuilderFrameTargets])
  | forRange slot lower upper body origin =>
    obtain ⟨localVar, integer, lowerStart, lowerFinish, upperFinish, bodyType,
      _, lowerSource, upperSource, _, bodySource, _⟩ := tyStmt_forRange_children source
    let le := lowerEnv env.mod env.vars results
    let low := lowerExpr lower le before
    let high := lowerExpr upper le low.2
    let kind := intTyOf low.1 le high.2
    have lowGenerated := generated.lowerExpr lower (show lowerExpr lower le before = low from rfl)
    have highGenerated := lowGenerated.lowerExpr upper (show lowerExpr upper le low.2 = high from rfl)
    have kindGenerated := highGenerated.intTyOf low.1 (show intTyOf low.1 le high.2 = kind from rfl)
    apply (replacementSites_lowerExpr (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) lower sourceTypes lowerSource results generated).bind
    apply (replacementSites_lowerExpr (location := (location.child 1 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) upper sourceTypes upperSource results lowGenerated).bind
    apply ReplacementSitesAt.whenLive
    intro block live
    apply (ReplacementSitesAt.intTyOf _ _ _).bind
    apply ReplacementSitesAt.header_generated (α := Unit) (le := le) (before := kind.2)
      (tail := fun header parameters => lowerRange kind.1 (parameters.headD 0) high.1 header
        (fun depth exit => lowerBlock (some ⟨depth, exit, .next header kind.1 (parameters.headD 0)⟩)
          [(slot, parameters.headD 0, origin)] false body)) [.data (.int kind.1)] [low.1] kindGenerated
    intro header parameters state current headerBound
    apply ReplacementSitesAt.lowerRange_generated _ _ _ _ (by simp) current
    intro depth exit bodyState bodyGenerated exitBound grows
    have headerLater : header < bodyState.blocks.size := Nat.lt_of_lt_of_le headerBound
      (Nat.le_trans ((dense_emitDef (.cmp .lt kind.1 (parameters.headD 0) high.1)
        le state _ _ rfl current.dense current.live).2.2) grows)
    exact replacementSites_lowerBlock (location := (location.child 2 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) body (sourceTypes.tables
      (after := { env with loops := env.loops + 1, visible := slot :: env.visible }) rfl rfl) bodySource results
      (some ⟨depth, exit, .next header kind.1 (parameters.headD 0)⟩)
      [(slot, parameters.headD 0, origin)] false bodyGenerated ⟨exitBound, headerLater⟩
      (by simp [ReplacementLoopTargetsIncluded, LoopBuilderFrameTargets])
  | forEach slot index view byReference body origin =>
    apply replacementSites_forEach_source sourceTypes source
    · intro element writable first last childSource state current
      exact replacementSites_lowerView (location := (location.child 0 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) view sourceTypes childSource results current
    · intro childTargets type first last childSource childLoop pre state current childBounds childAllowed
      exact replacementSites_lowerBlock (location := (location.child 1 _ (by simp [DemandNode.child?, DemandNode.children]))) (targets := _) body (sourceTypes.tables
        (after := { env with loops := env.loops + 1, visible := slot :: index.toList ++ env.visible })
        rfl rfl) childSource results childLoop pre false current childBounds childAllowed
    · exact generated

termination_by sizeOf statement

end

#print axioms replacementSites_lowerExpr
#print axioms replacementSites_lowerStmt
#print axioms replacementSites_lowerBlock

end Goose.Lower.Validation
