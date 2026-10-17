import Goose.Lower.Validation.CfgEdgeJoins
import Goose.Lower.Validation.CfgEdgeScalarActions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def CounterHeader (state : LS) (header : BlockId) (ty : IntTy) (counter : ValueId) : Prop :=
  ∃ body, state.blocks[header]? = some body ∧ body.params = [(counter, .data (.int ty))]

theorem CounterHeader.extend {before after : LS} (extension : EdgeExtension before after)
    {header : BlockId} {ty : IntTy} {counter : ValueId} (frame : CounterHeader before header ty counter) :
    CounterHeader after header ty counter := by
  obtain ⟨body, row, params⟩ := frame
  obtain ⟨next, nextRow, same, _⟩ := extension.blocks.2 header body row
  exact ⟨next, nextRow, same.trans params⟩

theorem CounterHeader.arguments {state : LS} {header : BlockId} {ty : IntTy} {counter value : ValueId}
    (frame : CounterHeader state header ty counter)
    (typed : state.vals[value]? = some (some (.data (.int ty)))) : EdgeArguments state header [value] := by
  obtain ⟨body, row, params⟩ := frame
  refine ⟨body, row, by simp [params], ?_⟩
  intro pair member
  simp only [params, List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at member
  subst pair
  exact typed

def LoopEdgeArguments (context : Option LoopCtx) (state : LS) : Prop :=
  match context with
  | none => True
  | some loop => EdgeArguments state loop.breakTo [] ∧
      match loop.cont with
      | .jump header => EdgeArguments state header []
      | .next header ty counter => CounterHeader state header ty counter ∧
          state.vals[counter]? = some (some (.data (.int ty)))

theorem LoopEdgeArguments.extend {context : Option LoopCtx} {before after : LS}
    (extension : EdgeExtension before after) (loop : LoopEdgeArguments context before) : LoopEdgeArguments context after := by
  cases context with
  | none => trivial
  | some context =>
    refine ⟨loop.1.extend extension, ?_⟩
    cases kind : context.cont with
    | jump header =>
      have edge : EdgeArguments before header [] := by simpa [kind] using loop.2
      exact edge.extend extension
    | next header ty counter =>
      have frame : CounterHeader before header ty counter ∧ before.vals[counter]? = some (some (.data (.int ty))) := by
        simpa [kind] using loop.2
      exact ⟨frame.1.extend extension, extension.types _ _ frame.2⟩

theorem edge_emitDef_recorded {env : LEnv} {before after : LS} {block : BlockId}
    {op : Op} {ty : VTy} {value : ValueId} (current : before.cur = some block)
    (typed : op.resultTy (tyEnv env before) = .ok ty)
    (run : emitDef op env before = (value, after)) : after.vals[value]? = some (some ty) := by
  rw [emitDef_run op env current] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  simp [typed, Except.toOption]

theorem edge_next_recorded {env : LEnv} {before after : LS} {block : BlockId}
    {ty : IntTy} {counter value : ValueId} (current : before.cur = some block)
    (typed : before.vals[counter]? = some (some (.data (.int ty))))
    (run : emitDef (.next ty counter) env before = (value, after)) :
    after.vals[value]? = some (some (.data (.int ty))) := by
  apply edge_emitDef_recorded current ?_ run
  have source : (tyEnv env before).valTy counter = .ok (.data (.int ty)) := by
    simp [TyEnv.valTy, tyEnv, typed]
  simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, source, pure, Except.pure, bind, Except.bind]

theorem edge_rangeBack_at (ty : IntTy) (counter : ValueId) (header : BlockId)
    (env : LEnv) (before after : LS) (result : Unit)
    (run : rangeBack ty counter header env before = (result, after))
    (checked : BuilderEdgeArguments before) (frame : CounterHeader before header ty counter)
    (typed : before.vals[counter]? = some (some (.data (.int ty)))) :
    EdgeExtension before after ∧ BuilderEdgeArguments after := by
  unfold rangeBack at run
  obtain ⟨live, middle, tested, tail⟩ := bind_eq.mp run
  have stable : middle = before := by
    change (before.cur.isSome, before) = (live, middle) at tested
    exact (Prod.mk.inj tested).2.symm
  subst middle
  cases live with
  | false =>
    simp only [Bool.false_eq_true, ite_false, pure_run] at tail
    obtain ⟨_, rfl⟩ := Prod.mk.inj tail
    exact ⟨.refl before, checked⟩
  | true =>
    simp only [ite_true, bind_eq] at tail
    obtain ⟨value, middle, nextRun, branchRun⟩ := tail
    have live : before.cur.isSome = true := (Prod.mk.inj tested).1
    obtain ⟨block, current⟩ : ∃ block, before.cur = some block := by
      cases current : before.cur with
      | none => simp [current] at live
      | some block => exact ⟨block, rfl⟩
    have nextTyped := edge_next_recorded current typed nextRun
    obtain ⟨nextExtension, nextChecked⟩ := edge_emitDef (.next ty counter) env before value middle nextRun checked
    have arguments := (frame.extend nextExtension).arguments nextTyped
    obtain ⟨lastExtension, lastChecked⟩ := edge_emitTerm_at (.br header [value]) env middle after result branchRun nextChecked (fun _ => arguments)
    exact ⟨nextExtension.trans lastExtension, lastChecked⟩

theorem edge_newBlock1_counterHeader {env : LEnv} {before after : LS} {result : BlockId × List ValueId}
    {ty : IntTy} (run : newBlock [.data (.int ty)] env before = (result, after)) :
    CounterHeader after result.1 ty (result.2.headD 0) := by
  rw [newBlock1_run] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  exact ⟨⟨[(before.vals.size, .data (.int ty))], #[]⟩, by simp, rfl⟩

theorem edge_lowerBreak_at (context : Option LoopCtx) (origin : OriginId)
    (env : LEnv) (before after : LS) (result : Unit)
    (run : lowerStmt context (.brk origin) env before = (result, after))
    (checked : BuilderEdgeArguments before) (loop : LoopEdgeArguments context before) :
    EdgeExtension before after ∧ BuilderEdgeArguments after := by
  cases context with
  | none => exact EdgeRun.pure () env before result after run checked
  | some context =>
    obtain ⟨ignored, prepared, leaveRun, branchRun⟩ := bind_eq.mp run
    obtain ⟨leaveExtension, leaveChecked⟩ := edge_leaveTo context.depth env before ignored prepared leaveRun checked
    have arguments := loop.1.extend leaveExtension
    obtain ⟨lastExtension, lastChecked⟩ := edge_emitTerm_at (.br context.breakTo []) env prepared after result branchRun leaveChecked (fun _ => arguments)
    exact ⟨leaveExtension.trans lastExtension, lastChecked⟩

theorem edge_lowerContinue_at (context : Option LoopCtx) (origin : OriginId)
    (env : LEnv) (before after : LS) (result : Unit)
    (run : lowerStmt context (.cont origin) env before = (result, after))
    (checked : BuilderEdgeArguments before) (loop : LoopEdgeArguments context before) :
    EdgeExtension before after ∧ BuilderEdgeArguments after := by
  cases context with
  | none => exact EdgeRun.pure () env before result after run checked
  | some context =>
    cases kind : context.cont with
    | jump header =>
      have arguments : EdgeArguments before header [] := by simpa [kind] using loop.2
      simp only [lowerStmt, kind, bind_eq] at run
      obtain ⟨ignored, prepared, leaveRun, branchRun⟩ := run
      obtain ⟨leaveExtension, leaveChecked⟩ := edge_leaveTo context.depth env before ignored prepared leaveRun checked
      obtain ⟨lastExtension, lastChecked⟩ := edge_emitTerm_at (.br header []) env prepared after result branchRun leaveChecked
        (fun _ => arguments.extend leaveExtension)
      exact ⟨leaveExtension.trans lastExtension, lastChecked⟩
    | next header ty counter =>
      have frame : CounterHeader before header ty counter ∧ before.vals[counter]? = some (some (.data (.int ty))) := by
        simpa [kind] using loop.2
      simp only [lowerStmt, kind, bind_eq] at run
      obtain ⟨ignored, prepared, leaveRun, value, incremented, nextRun, branchRun⟩ := run
      obtain ⟨leaveExtension, leaveChecked⟩ := edge_leaveTo context.depth env before ignored prepared leaveRun checked
      have preparedFrame := frame.1.extend leaveExtension
      have preparedTyped := leaveExtension.types counter (.data (.int ty)) frame.2
      obtain ⟨nextExtension, nextChecked⟩ := edge_emitDef (.next ty counter) env prepared value incremented nextRun leaveChecked
      have arguments : incremented.cur.isSome = true → BuilderTermArguments incremented (.br header [value]) := by
        intro live
        cases current : prepared.cur with
        | none =>
          rw [emitDef_none _ env current] at nextRun
          obtain ⟨_, rfl⟩ := Prod.mk.inj nextRun
          simp [current] at live
        | some block =>
          have nextTyped := edge_next_recorded current preparedTyped nextRun
          exact (preparedFrame.extend nextExtension).arguments nextTyped
      obtain ⟨lastExtension, lastChecked⟩ := edge_emitTerm_at (.br header [value]) env incremented after result branchRun nextChecked arguments
      exact ⟨leaveExtension.trans (nextExtension.trans lastExtension), lastChecked⟩

end Goose.Lower.Validation
