import Goose.Lower.Validation.EmittedMetadataControlStatements

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem metadata_source_forRange {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (slot : VarId) (lo hi : Expr) (body : Core.Block) (origin : OriginId)
    (lowChild : EmittedMetadataSourceExpression env results lo) (highChild : EmittedMetadataSourceExpression env results hi)
    (bodyChild : ∀ env, EmittedMetadataSourceBlock env results body) :
    EmittedMetadataSourceStatement env results scope (.forRange slot lo hi body origin) := by
  intro resultTypes output start finish source loop before result after generated loopBounds loopTypes run builder
  obtain ⟨localVar, integer, lowerStart, lowerFinish, upperFinish, bodyType,
    declared, lowSource, highSource, binderType, bodySource, _⟩ := tyStmt_forRange_children source
  let le := lowerEnv env.mod env.vars results
  let low := lowerExpr lo le before
  let high := lowerExpr hi le low.2
  have lowBuilder := lowChild resultTypes lowSource before low.1 low.2 generated trivial trivial rfl builder
  have lowGenerated : GeneratedBuilderState low.2 := generated.lowerExpr lo rfl
  have highBuilder := highChild resultTypes highSource low.2 high.1 high.2 lowGenerated trivial trivial rfl lowBuilder
  have highGenerated : GeneratedBuilderState high.2 := lowGenerated.lowerExpr hi rfl
  have afterEq : after = (lowerStmt loop (.forRange slot lo hi body origin) le before).2 := (congrArg Prod.snd run).symm
  rw [afterEq]
  change EmittedMetadata le ((whenLive () fun _ => do
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
    have checked := metadata_control_rangeHeader highBuilder highGenerated integer low.1 high.1 retainedLow highTyped
      (fun header counter depth target => lowerBlock (some ⟨depth, target, .next header integer counter⟩)
        [(slot, counter, origin)] false body)
      (fun header counter depth target started builder generated counterTyped prefixProof headerBound targetBound active => by
        have targets : LoopBuilderTargets (some ⟨depth, target, .next header integer counter⟩) started := ⟨targetBound, headerBound⟩
        have types : EmittedLoopTypes (some ⟨depth, target, .next header integer counter⟩) started := counterTyped
        have slotAt : le.slots[slot]? = some ⟨localVar.ty, localVar.kind, localVar.scope, slot⟩ := by
          have localAt := (declare_ok _ _ _ _ _ declared).2.1
          simp [le, lowerEnv, Array.getElem?_mapIdx, localAt]
        have preTyped : EmittedPreTyped le started [(slot, counter, origin)] := by
          intro x value org member
          have same := List.mem_singleton.mp member
          cases same
          exact ⟨⟨localVar.ty, localVar.kind, localVar.scope, slot⟩, slotAt, by simpa only [binderType] using counterTyped⟩
        exact ⟨bodyChild { env with loops := env.loops + 1, visible := slot :: env.visible } resultTypes bodySource
          _ [(slot, counter, origin)] false started _ _ generated targets types preTyped rfl builder,
          generated.lowerBlock _ _ false body targets rfl⟩)
      (fun header counter depth target => advB_lowerBlock _ [(slot, counter, origin)] false body)
      (fun header counter depth target => types_lowerBlock _ [(slot, counter, origin)] false body)
    rw [whenLive_some _ _ _ live]
    simp only [bind_run]
    rw [integerRead]
    simpa only [bind_run] using checked.1

end Goose.Lower.Validation
