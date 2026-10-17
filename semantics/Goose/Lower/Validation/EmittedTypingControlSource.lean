import Goose.Lower.Validation.EmittedTypingBlockSource
import Goose.Lower.Validation.EmittedTypingGeneratedBranches
import Goose.Lower.Validation.EmittedTypingGeneratedHeaders
import Goose.Lower.Validation.SourceStatementTypingControl
import Goose.Lower.Validation.EmittedTypingSourceOutputs

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitted_source_conditional {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (condition : Expr) (yes : Core.Block) (otherwise : Option Core.Block) (origin : OriginId)
    (conditionChild : EmittedSourceExpression env results condition)
    (yesChild : ∀ env, EmittedSourceBlock env results yes)
    (otherwiseChild : ∀ body, otherwise = some body → ∀ env, EmittedSourceBlock env results body) :
    EmittedSourceStatement env results scope (.ifS condition yes otherwise origin) := by
  intro output start finish source initial before loop generated builder loopTypes loopBounds active
  obtain ⟨conditionFinish, yesType, yesFinish, conditionSource, yesSource, otherwiseSource, _⟩ := tyStmt_if_children source
  let le := lowerEnv env.mod env.vars results
  let evaluated := lowerExpr condition le before
  have conditionBuilder := conditionChild conditionSource generated builder
  have conditionGenerated : GeneratedBuilderState evaluated.2 := generated.lowerExpr condition rfl
  have conditionTypes := loopTypes.retained (types_lowerExpr condition le before _ _ rfl)
  have conditionTargets := loopBounds.mono (advB_lowerExpr condition le before _ _ rfl).ext.1
  cases otherwise with
  | none =>
    have checked := emitted_checked_generated_ifThen conditionBuilder conditionGenerated evaluated.1
      (value_lowerExpr condition le before _ _ rfl) (lowerBlock loop [] false yes)
      (fun initial started builder generated retained grows => by
        have targets := conditionTargets.mono grows
        exact ⟨yesChild env yesSource loop [] false generated builder (conditionTypes.retained retained) targets
          (by intro slot value origin member; cases member), generated.lowerBlock loop [] false yes targets rfl⟩)
      (advB_lowerBlock loop [] false yes)
    exact checked.1
  | some no =>
    obtain ⟨noType, noSource⟩ := otherwiseSource
    have checked := emitted_checked_generated_ifArms conditionBuilder conditionGenerated evaluated.1
      (value_lowerExpr condition le before _ _ rfl) (lowerBlock loop [] false yes) (lowerBlock loop [] false no)
      (fun initial started builder generated retained grows => by
        have targets := conditionTargets.mono grows
        exact ⟨yesChild env yesSource loop [] false generated builder (conditionTypes.retained retained) targets
          (by intro slot value origin member; cases member), generated.lowerBlock loop [] false yes targets rfl⟩)
      (fun initial started builder generated retained grows => by
        have targets := conditionTargets.mono grows
        exact ⟨otherwiseChild no rfl env noSource loop [] false generated builder (conditionTypes.retained retained) targets
          (by intro slot value origin member; cases member), generated.lowerBlock loop [] false no targets rfl⟩)
      (advB_lowerBlock loop [] false yes) (advB_lowerBlock loop [] false no) (types_lowerBlock loop [] false yes)
    exact checked.1

theorem emitted_source_while {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (condition : Expr) (body : Core.Block) (origin : OriginId)
    (conditionChild : EmittedSourceExpression env results condition)
    (bodyChild : ∀ env, EmittedSourceBlock env results body) :
    EmittedSourceStatement env results scope (.while condition body origin) := by
  intro output start finish source initial before loop generated builder loopTypes loopBounds active
  obtain ⟨conditionFinish, bodyType, conditionSource, bodySource, _⟩ := tyStmt_while_children source
  have checked := emitted_checked_generated_whileHeader builder generated (lowerExpr condition)
    (fun header depth target => lowerBlock (some ⟨depth, target, .jump header⟩) [] false body)
    (fun initial started builder generated =>
      ⟨conditionChild conditionSource generated builder, generated.lowerExpr condition rfl⟩)
    (value_lowerExpr condition) (advB_lowerExpr condition)
    (fun header depth target initial started builder generated headerBound targetBound => by
      have targets : LoopBuilderTargets (some ⟨depth, target, .jump header⟩) started := ⟨targetBound, headerBound⟩
      exact ⟨bodyChild { env with loops := env.loops + 1 } bodySource (some ⟨depth, target, .jump header⟩) [] false
        generated builder trivial targets (by intro slot value origin member; cases member),
        generated.lowerBlock _ [] false body targets rfl⟩)
    (fun header depth target => advB_lowerBlock (some ⟨depth, target, .jump header⟩) [] false body)
    (fun header depth target => types_lowerBlock (some ⟨depth, target, .jump header⟩) [] false body)
  exact checked.1

theorem emitted_source_forRange {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (slot : VarId) (lo hi : Expr) (body : Core.Block) (origin : OriginId)
    (lowChild : EmittedSourceExpression env results lo) (highChild : EmittedSourceExpression env results hi)
    (bodyChild : ∀ env, EmittedSourceBlock env results body) :
    EmittedSourceStatement env results scope (.forRange slot lo hi body origin) := by
  intro output start finish source initial before loop generated builder loopTypes loopBounds active
  obtain ⟨localVar, integer, lowerStart, lowerFinish, upperFinish, bodyType,
    declared, lowSource, highSource, binderType, bodySource, _⟩ := tyStmt_forRange_children source
  let le := lowerEnv env.mod env.vars results
  let low := lowerExpr lo le before
  let high := lowerExpr hi le low.2
  have lowBuilder := lowChild lowSource generated builder
  have lowGenerated : GeneratedBuilderState low.2 := generated.lowerExpr lo rfl
  have highBuilder := highChild highSource lowGenerated lowBuilder
  have highGenerated : GeneratedBuilderState high.2 := lowGenerated.lowerExpr hi rfl
  change EmittedBuilder le initial ((whenLive () fun _ => do
    let hint ← intTyOf low.1
    let (header, params) ← newBlock [.data (.int hint)]
    let counter := params.headD 0
    emitTerm (.br header [low.1])
    setCur (some header)
    lowerRange hint counter high.1 header (fun depth target =>
      lowerBlock (some ⟨depth, target, .next header hint counter⟩) [(slot, counter, origin)] false body)) le high.2).2
  cases live : high.2.cur with
  | none =>
    rw [whenLive_none _ _ _ live]
    exact highBuilder
  | some current =>
    have highLive : high.2.cur.isSome = true := by simp [live]
    have lowLive := (dead_lowerExpr hi).live_before rfl highLive
    have lowTyped := lowerExpr_generated_typed lo lowSource (show lowerExpr lo le before = low from rfl) lowLive generated
    have retainedLow := (types_lowerExpr hi le low.2 _ _ rfl) _ _ lowTyped
    have highTyped := lowerExpr_generated_typed hi highSource (show lowerExpr hi le low.2 = high from rfl) highLive lowGenerated
    have integerRead : intTyOf low.1 le high.2 = (integer, high.2) := intTyOf_recorded (le := le) retainedLow
    have checked := emitted_checked_generated_rangeHeader highBuilder highGenerated integer low.1 high.1 retainedLow highTyped
      (fun header counter depth target => lowerBlock (some ⟨depth, target, .next header integer counter⟩)
        [(slot, counter, origin)] false body)
      (fun header counter depth target initial started builder generated counterTyped prefixProof headerBound targetBound => by
        have targets : LoopBuilderTargets (some ⟨depth, target, .next header integer counter⟩) started := ⟨targetBound, headerBound⟩
        have types : EmittedLoopTypes (some ⟨depth, target, .next header integer counter⟩) started := counterTyped
        have preBounds : ∀ x value org, (x, value, org) ∈ [(slot, counter, origin)] → value < started.vals.size := by
          intro x value org member
          have same : value = counter := congrArg (fun triple => triple.2.1) (List.mem_singleton.mp member)
          rw [same]
          exact (Array.getElem?_eq_some_iff.mp counterTyped).1
        exact ⟨bodyChild { env with loops := env.loops + 1, visible := slot :: env.visible } bodySource
          _ [(slot, counter, origin)] false generated builder types targets preBounds,
          generated.lowerBlock _ _ false body targets rfl⟩)
      (fun header counter depth target => advB_lowerBlock _ [(slot, counter, origin)] false body)
      (fun header counter depth target => types_lowerBlock _ [(slot, counter, origin)] false body)
    rw [whenLive_some _ _ _ live]
    simp only [bind_run]
    rw [integerRead]
    simpa only [bind_run] using checked.1

end Goose.Lower.Validation
