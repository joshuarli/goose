import Goose.Lower.Validation.SummaryPreservationReplayLoopsSource
import Goose.Lower.Validation.DeadFrontier

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpStmt_range_children {env : PEnv} {indexVar : VarId} {low high : Expr} {body : Core.Block}
    {origin : OriginId} {before after : RState}
    (source : rpStmt env (.forRange indexVar low high body origin) before = .ok ((), after)) :
    ∃ lowStart lowRoots lowState highRoots highState bodyRoots bodyRange bodyState,
      rpExpr env low lowStart = .ok (lowRoots, lowState) ∧
      rpExpr env high lowState = .ok (highRoots, highState) ∧
      rpBlockValue env [] body highState = .ok ((bodyRoots, bodyRange), bodyState) := by
  simp only [rpStmt] at source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, lowStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨lowRoots, lowState, lowReplay, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨highRoots, highState, highReplay, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨result, bodyState, bodyReplay, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact ⟨lowStart, lowRoots, lowState, highRoots, highState, result.1, result.2,
    bodyState, lowReplay, highReplay, bodyReplay⟩

namespace ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

set_option maxHeartbeats 1200000

theorem range_statement {tenv output : TEnv} {env : PEnv} {indexVar : VarId} {low high : Expr}
    {body : Core.Block} {origin : OriginId} {scope start finish : Nat} {before after : RState}
    (loop : Option LoopCtx)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (typing : Core.tyStmt tenv scope (.forRange indexVar low high body origin) start = .ok (output, finish))
    (source : rpStmt env (.forRange indexVar low high body origin) before = .ok ((), after))
    (boundStep : ∀ expression, expression = low ∨ expression = high →
      ∀ integer typeStart typeFinish sourceBefore sourceAfter sourceRoots state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      Core.tyExpr tenv expression typeStart = .ok (.int integer, typeFinish) →
      rpExpr env expression sourceBefore = .ok (sourceRoots, sourceAfter) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots (lowerExpr expression le state).2 next ∧
        ((lowerExpr expression le state).2.cur.isSome = true →
          ReplayValue func next (lowerExpr expression le state).2 (lowerExpr expression le state).1
            sourceRoots (.data (.int integer))) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index)
    (bodyStep : ∀ depth header exit actualType counter typeStart bodyType sourceBefore sourceAfter bodyRoots bodyRange state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      header < state.blocks.size → exit < state.blocks.size →
      (∀ binding ∈ [(indexVar, counter, origin)], binding.2.1 < state.vals.size) →
      (∀ binding ∈ [(indexVar, counter, origin)], ∀ root ∈ rootsAt provenance.vals binding.2.1,
        root ∈ rootsAt slots binding.1) →
      Core.tyBlock { tenv with loops := tenv.loops + 1, visible := indexVar :: tenv.visible } [] body typeStart =
        .ok (bodyType, finish) →
      rpBlockValue env [] body sourceBefore = .ok ((bodyRoots, bodyRange), sourceAfter) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerBlock (some ⟨depth, exit, .next header actualType counter⟩)
            [(indexVar, counter, origin)] false body le state).2 next ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerStmt loop (.forRange indexVar low high body origin) le ls).2 next ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨localVar, integer, lowTypeStart, lowTypeFinish, highTypeFinish, bodyType,
      declaration, lowTyped, highTyped, localType, bodyTyped, _⟩ := tyStmt_forRange_children typing
  obtain ⟨lowStart, lowRoots, lowState, highRoots, highState, bodyRoots, bodyRange, bodyState,
      lowReplay, highReplay, bodyReplay⟩ := rpStmt_range_children source
  let loweredLow := lowerExpr low le ls
  obtain ⟨lowProv, lowReady, lowValue, lowGrowth⟩ := boundStep low (Or.inl rfl) integer
    lowTypeStart lowTypeFinish lowStart lowState lowRoots ls upper ready lowTyped lowReplay
  let loweredHigh := lowerExpr high le loweredLow.2
  obtain ⟨highProv, highReady, highValue, highGrowth⟩ := boundStep high (Or.inr rfl) integer
    lowTypeFinish highTypeFinish lowState highState highRoots loweredLow.2 lowProv lowReady highTyped highReplay
  have lowAdv := advB_lowerExpr low le ls loweredLow.1 loweredLow.2 rfl
  have highAdv := advB_lowerExpr high le loweredLow.2 loweredHigh.1 loweredHigh.2 rfl
  have oldToHigh : upper.vals.size ≤ highProv.vals.size := by
    rw [ready.roots.valueSize, highReady.roots.valueSize]
    exact Nat.le_trans lowAdv.vals highAdv.vals
  have oldToLow : upper.vals.size ≤ lowProv.vals.size := by
    rw [ready.roots.valueSize, lowReady.roots.valueSize]
    exact lowAdv.vals
  cases current : loweredHigh.2.cur with
  | none =>
    have whole : lowerStmt loop (.forRange indexVar low high body origin) le ls = ((), loweredHigh.2) := by
      simp only [lowerStmt, bind_run]
      change whenLive () _ le loweredHigh.2 = ((), loweredHigh.2)
      exact whenLive_none _ _ _ current
    refine ⟨highProv, by simpa only [whole] using highReady, ?_⟩
    intro index bound
    rw [highGrowth index (Nat.lt_of_lt_of_le bound oldToLow), lowGrowth index bound]
  | some block =>
    have highLive : loweredHigh.2.cur.isSome = true := by simp [current]
    have lowLive := (dead_lowerExpr high).live_before
      (show lowerExpr high le loweredLow.2 = (loweredHigh.1, loweredHigh.2) from rfl) highLive
    have first := lowValue lowLive
    have last := highValue highLive
    have firstBound := Nat.lt_of_lt_of_le first.bound highAdv.vals
    have firstOld : loweredLow.1 < lowProv.vals.size := by simpa only [lowReady.roots.valueSize] using first.bound
    have firstScalar : rootsAt highProv.vals loweredLow.1 = [] :=
      (highGrowth loweredLow.1 firstOld).trans (first.scalar rfl)
    cases typeRun : intTyOf loweredLow.1 le loweredHigh.2 with
    | mk actualType typeState =>
      have stateEq := intTyOf_eq typeRun
      subst typeState
      let allocated := newBlock [.data (.int actualType)] le loweredHigh.2
      obtain ⟨headerProv, headerReady, counterScalar, headerGrowth⟩ := highReady.loopScalarBlock (.data (.int actualType))
      let counter := allocated.1.2.headD 0
      have counterEq : counter = loweredHigh.2.vals.size := by simp [counter, allocated, newBlock1_run]
      have headerBound : allocated.1.1 < allocated.2.blocks.size := by simp [allocated, newBlock1_run]
      have counterBound : counter < allocated.2.vals.size := by simp [counterEq, allocated, newBlock1_run]
      have firstInHigh : loweredLow.1 < highProv.vals.size := by simpa only [highReady.roots.valueSize] using firstBound
      have firstAfterHeader : rootsAt headerProv.vals loweredLow.1 = [] :=
        (headerGrowth loweredLow.1 firstInHigh).trans firstScalar
      let bridged := emitTerm (.br allocated.1.1 [loweredLow.1]) le allocated.2
      have bridgeReady := headerReady.loopBranch allocated.1.1 [loweredLow.1] headerBound
        (by simpa [allocated, newBlock1_run] using Nat.lt_succ_of_lt firstBound) (by simpa using firstAfterHeader)
      have bridgeAdv := advB_emitTerm (.br allocated.1.1 [loweredLow.1]) le allocated.2 bridged.1 bridged.2 rfl
      have headerStill := Nat.lt_of_lt_of_le headerBound bridgeAdv.ext.1
      have counterStill := Nat.lt_of_lt_of_le counterBound bridgeAdv.vals
      have lastStill : loweredHigh.1 < bridged.2.vals.size := by
        apply Nat.lt_of_lt_of_le last.bound
        exact Nat.le_trans
          (advB_newBlock1 (.data (.int actualType)) le loweredHigh.2 allocated.1 allocated.2 rfl).vals bridgeAdv.vals
      let started := (Goose.Lower.setCur (some allocated.1.1) le bridged.2).2
      have startedReady := bridgeReady.setCur (some allocated.1.1) (by intro b row; cases row; exact headerStill)
      have startedLive : started.cur.isSome = true := by rfl
      have counterRoots : rootsAt headerProv.vals counter = [] := by simpa only [counterEq] using counterScalar
      obtain ⟨next, nextReady, growth⟩ := startedReady.loopRange actualType counter loweredHigh.1 allocated.1.1
        (fun depth exit => lowerBlock (some ⟨depth, exit, .next allocated.1.1 actualType counter⟩)
          [(indexVar, counter, origin)] false body) startedLive headerStill counterStill lastStill counterRoots
        (fun _ _ => advB_lowerBlock _ _ _ _)
        (by
          intro depth exit state provenance stateReady headerBound exitBound counterBound counterScalar
          apply bodyStep depth allocated.1.1 exit actualType counter highTypeFinish bodyType
            highState bodyState bodyRoots bodyRange state provenance stateReady headerBound exitBound
          · simpa using counterBound
          · intro binding member root rootMember
            have same := List.mem_singleton.mp member
            subst binding
            rw [counterScalar] at rootMember
            cases rootMember
          · exact bodyTyped
          · exact bodyReplay)
      have whole : lowerStmt loop (.forRange indexVar low high body origin) le ls =
          lowerRange actualType counter loweredHigh.1 allocated.1.1
            (fun depth exit => lowerBlock (some ⟨depth, exit, .next allocated.1.1 actualType counter⟩)
              [(indexVar, counter, origin)] false body) le started := by
        simp only [lowerStmt, bind_run]
        change whenLive () _ le loweredHigh.2 = _
        rw [whenLive_some _ _ _ current]
        simp only [bind_run]
        rw [typeRun]
      refine ⟨next, by simpa only [whole] using nextReady, ?_⟩
      intro index oldBound
      have highBound := Nat.lt_of_lt_of_le oldBound oldToHigh
      have headerBound : index < headerProv.vals.size := by
        rw [headerReady.roots.valueSize]
        exact Nat.lt_of_lt_of_le (by simpa only [highReady.roots.valueSize] using highBound)
          (by simp [allocated, newBlock1_run])
      rw [growth index headerBound, headerGrowth index highBound,
        highGrowth index (Nat.lt_of_lt_of_le oldBound oldToLow), lowGrowth index oldBound]

end ReplayBuilder

#print axioms rpStmt_range_children
#print axioms ReplayBuilder.range_statement

end Goose.Lower.Validation.SummaryPreservation
