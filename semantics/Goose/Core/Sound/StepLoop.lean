import Goose.Core.Sound.StepUse

/-!
One step of the induction on fuel for the three loops.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {plans : Array (Array DemandPoint)} {n : Nat}

/-- The value an index variable of a loop over a run is bound to. -/
def idxVal (i : Nat) (idx : Option VarId) : List (VarId × Val) :=
  match idx with
  | some j => [(j, Val.int .i64 i)]
  | none => []

theorem evalExpr_bool (k : Nat) (cfg : Cfg) (env : Env) (b : Bool) :
    evalExpr k cfg env (.bool b) = if k = 0 then timeout else pure (.bool b) := by
  cases k <;> simp [evalExpr]

/-- One iteration of a loop over a run, with the two choices it makes pulled
out of the continuation. -/
theorem execEach_eq (k : Nat) (cfg : Cfg) (env : Env) (x : VarId) (idx : Option VarId) (byRef : Bool)
    (body : Block) (vw : ViewVal) (i : Nat) :
    execEach (k + 1) cfg env x idx byRef body vw i =
      ((if vw.resizable = true then lengthLoc vw.loc else pure vw.len) >>= fun len =>
        if i < len then
          ((if byRef = true then pure (Val.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩)
            else readLoc ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩) >>= fun ev =>
          execBlock k cfg env ((x, ev) :: (match idx with
              | some j => [(j, Val.int .i64 i)]
              | none => [])) body >>= fun fl =>
            match fl with
            | .normal _ => execEach k cfg env x idx byRef body vw (i + 1)
            | .cont => execEach k cfg env x idx byRef body vw (i + 1)
            | .brk => pure (.normal .unit)
            | .ret v => pure (.ret v))
        else pure (.normal .unit)) := by
  conv => lhs; unfold execEach
  cases vw.resizable <;> cases byRef <;> rfl

private noncomputable def whileCondContext {path : List Nat} {c : Expr} {body : Block} {origin : OriginId}
    (ec : EvaluationContext m plans path (.statement (.while c body origin)) .statement) :
    EvaluationContext m plans (path ++ [0]) (.expression c) .expression := by
  exact ec.child (by simp [DemandNode.primaryPhase]) 0 _ _
    (by simp [DemandNode.child?, DemandNode.children])
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])

private noncomputable def whileBodyContext {path : List Nat} {c : Expr} {body : Block} {origin : OriginId}
    (ec : EvaluationContext m plans path (.statement (.while c body origin)) .statement) :
    EvaluationContext m plans (path ++ [1]) (.block body) .block := by
  exact ec.child (by simp [DemandNode.primaryPhase]) 1 _ _
    (by simp [DemandNode.child?, DemandNode.children])
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])

private noncomputable def rangeLowerContext {path : List Nat} {x : VarId} {lower upper : Expr}
    {body : Block} {origin : OriginId}
    (ec : EvaluationContext m plans path
      (.statement (.forRange x lower upper body origin)) .statement) :
    EvaluationContext m plans (path ++ [0]) (.expression lower) .expression := by
  exact ec.child (by simp [DemandNode.primaryPhase]) 0 _ _
    (by simp [DemandNode.child?, DemandNode.children])
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])

private noncomputable def rangeUpperContext {path : List Nat} {x : VarId} {lower upper : Expr}
    {body : Block} {origin : OriginId}
    (ec : EvaluationContext m plans path
      (.statement (.forRange x lower upper body origin)) .statement) :
    EvaluationContext m plans (path ++ [1]) (.expression upper) .expression := by
  exact ec.child (by simp [DemandNode.primaryPhase]) 1 _ _
    (by simp [DemandNode.child?, DemandNode.children])
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])

private noncomputable def rangeBodyContext {path : List Nat} {x : VarId} {lower upper : Expr}
    {body : Block} {origin : OriginId}
    (ec : EvaluationContext m plans path
      (.statement (.forRange x lower upper body origin)) .statement) :
    EvaluationContext m plans (path ++ [2]) (.block body) .block := by
  exact ec.child (by simp [DemandNode.primaryPhase]) 2 _ _
    (by simp [DemandNode.child?, DemandNode.children])
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])

private noncomputable def eachViewContext {path : List Nat} {x : VarId} {idx : Option VarId}
    {sourceView : View} {byRef : Bool} {body : Block} {origin : OriginId}
    (ec : EvaluationContext m plans path
      (.statement (.forEach x idx sourceView byRef body origin)) .statement) :
    EvaluationContext m plans (path ++ [0]) (.view sourceView) .view := by
  exact ec.child (by simp [DemandNode.primaryPhase]) 0 _ _
    (by simp [DemandNode.child?, DemandNode.children])
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])

private noncomputable def eachBodyContext {path : List Nat} {x : VarId} {idx : Option VarId}
    {sourceView : View} {byRef : Bool} {body : Block} {origin : OriginId}
    (ec : EvaluationContext m plans path
      (.statement (.forEach x idx sourceView byRef body origin)) .statement) :
    EvaluationContext m plans (path ++ [1]) (.block body) .block := by
  exact ec.child (by simp [DemandNode.primaryPhase]) 1 _ _
    (by simp [DemandNode.child?, DemandNode.children])
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])

private theorem whileCondOutputFuture {path : List Nat} {c : Expr} {body : Block} {origin : OriginId}
    (ec : EvaluationContext m plans path (.statement (.while c body origin)) .statement) :
    (whileCondContext ec).outputFuture = match ec with
      | .pilot _ active => active
      | .shrink _ context =>
        (context.expected.frame.active.filter (c.variables ++ body.variables).contains) ++
          context.expected.frame.future := by
  cases ec with
  | pilot profile active =>
    simp [whileCondContext, EvaluationContext.child, EvaluationContext.outputFuture,
      DemandNode.visibleForChild, DemandNode.visibleAfter]
  | shrink profile context =>
    let transition := context.child (by simp [DemandNode.primaryPhase]) 0 (.expression c) .expression
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
    have hchild :
        (DemandNode.statement (.while c body origin)).childExpectation?
          ⟨context.expected.path, .expression, context.expected.frame.active,
            context.expected.frame.future, context.expected.frame.retained⟩ 0 = some
          ⟨context.expected.frame.active,
            (context.expected.frame.active.filter (c.variables ++ body.variables).contains) ++
              context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children,
        DemandNode.visibleForChild]
    have hfuture : transition.childFrame.future =
        (context.expected.frame.active.filter (c.variables ++ body.variables).contains) ++
          context.expected.frame.future := by
      have h := DemandNode.childFrame_future transition.childFrameEq hchild
      simpa [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children]
        using h
    change transition.context.expected.frame.future = _
    rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq, hfuture]

private theorem whileBodyOutputFuture {path : List Nat} {c : Expr} {body : Block} {origin : OriginId}
    (ec : EvaluationContext m plans path (.statement (.while c body origin)) .statement) :
    (whileBodyContext ec).outputFuture = match ec with
      | .pilot _ active => active
      | .shrink _ context =>
        (context.expected.frame.active.filter (c.variables ++ body.variables).contains) ++
          context.expected.frame.future := by
  cases ec with
  | pilot profile active =>
    simp [whileBodyContext, EvaluationContext.child, EvaluationContext.outputFuture,
      DemandNode.visibleForChild, DemandNode.visibleAfter]
  | shrink profile context =>
    let transition := context.child (by simp [DemandNode.primaryPhase]) 1 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
    have hchild :
        (DemandNode.statement (.while c body origin)).childExpectation?
          ⟨context.expected.path, .expression, context.expected.frame.active,
            context.expected.frame.future, context.expected.frame.retained⟩ 1 = some
          ⟨context.expected.frame.active,
            (context.expected.frame.active.filter (c.variables ++ body.variables).contains) ++
              context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children,
        DemandNode.visibleForChild]
    have hfuture : transition.childFrame.future =
        (context.expected.frame.active.filter (c.variables ++ body.variables).contains) ++
          context.expected.frame.future := by
      have h := DemandNode.childFrame_future transition.childFrameEq hchild
      simpa [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children]
        using h
    change transition.context.expected.frame.future = _
    rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq, hfuture]

private theorem whileCondInput_subset {path : List Nat} {c : Expr} {body : Block} {origin : OriginId}
    (ec : EvaluationContext m plans path (.statement (.while c body origin)) .statement) :
    ∀ x, x ∈ (whileCondContext ec).inputFuture → x ∈ ec.inputFuture := by
  cases ec with
  | pilot profile active =>
    intro x hx
    simp [whileCondContext, EvaluationContext.inputFuture, EvaluationContext.child,
      DemandNode.visibleForChild, DemandNode.variables, Stmt.variables] at hx
    have hinput : x ∈ ((c.variables ++ body.variables) ++ active) := by
      rcases hx with hcond | hactive
      · exact List.mem_append_left _ (List.mem_append_left _ hcond)
      · exact List.mem_append_right _ hactive
    simpa [EvaluationContext.inputFuture, DemandNode.variables, Stmt.variables] using hinput
  | shrink profile context =>
    intro x hx
    have hout := whileCondOutputFuture (ec := .shrink profile context)
    change x ∈ c.variables ++ (whileCondContext (.shrink profile context)).outputFuture at hx
    rw [hout] at hx
    simp only [EvaluationContext.inputFuture, NodeContext.inputFuture,
      DemandNode.variables, Stmt.variables]
    apply List.mem_append.mpr
    rcases List.mem_append.mp hx with hcond | hrest
    · exact Or.inl (List.mem_append_left _ hcond)
    · rcases List.mem_append.mp hrest with hbackedge | hfuture
      · simp only [List.mem_filter, List.contains_iff_mem] at hbackedge
        exact Or.inl hbackedge.2
      · exact Or.inr hfuture

private theorem whileBodyInput_subset {path : List Nat} {c : Expr} {body : Block} {origin : OriginId}
    (ec : EvaluationContext m plans path (.statement (.while c body origin)) .statement) :
    ∀ x, x ∈ (whileBodyContext ec).inputFuture → x ∈ ec.inputFuture := by
  cases ec with
  | pilot profile active =>
    intro x hx
    simp [whileBodyContext, EvaluationContext.inputFuture, EvaluationContext.child,
      DemandNode.visibleForChild, DemandNode.variables, Stmt.variables] at hx
    have hinput : x ∈ ((c.variables ++ body.variables) ++ active) := by
      rcases hx with hbody | hactive
      · exact List.mem_append_left _ (List.mem_append_right _ hbody)
      · exact List.mem_append_right _ hactive
    simpa [EvaluationContext.inputFuture, DemandNode.variables, Stmt.variables] using hinput
  | shrink profile context =>
    intro x hx
    have hout := whileBodyOutputFuture (ec := .shrink profile context)
    change x ∈ body.variables ++ (whileBodyContext (.shrink profile context)).outputFuture at hx
    rw [hout] at hx
    simp only [EvaluationContext.inputFuture, NodeContext.inputFuture,
      DemandNode.variables, Stmt.variables]
    apply List.mem_append.mpr
    rcases List.mem_append.mp hx with hbody | hrest
    · exact Or.inl (List.mem_append_right _ hbody)
    · rcases List.mem_append.mp hrest with hbackedge | hfuture
      · simp only [List.mem_filter, List.contains_iff_mem] at hbackedge
        exact Or.inl hbackedge.2
      · exact Or.inr hfuture

private theorem whileCondOutput_coversBodyInput {path : List Nat} {c : Expr} {body : Block}
    {origin : OriginId} {tenv : TEnv}
    (ec : EvaluationContext m plans path (.statement (.while c body origin)) .statement)
    (hactive : ec.ActiveMatches tenv) :
    ∀ x, x ∈ tenv.visible → x ∈ (whileBodyContext ec).inputFuture →
      x ∈ (whileCondContext ec).outputFuture := by
  cases ec with
  | pilot profile active =>
    intro x hvisible _
    simpa [whileCondContext, EvaluationContext.child, EvaluationContext.child_outputFuture,
      EvaluationContext.outputFuture, DemandNode.visibleForChild, DemandNode.visibleAfter] using
      (hactive x).2 hvisible
  | shrink profile context =>
    intro x hvisible hbody
    have hfuture := whileBodyOutputFuture (ec := .shrink profile context)
    change x ∈ body.variables ++ (whileBodyContext (.shrink profile context)).outputFuture at hbody
    rw [hfuture] at hbody
    simp only [EvaluationContext.outputFuture] at hbody
    rcases List.mem_append.mp hbody with hbodyVar | hrest
    · have hplanActive : x ∈ context.expected.frame.active := (hactive x).2 hvisible
      have hbackedge : x ∈ context.expected.frame.active.filter
          (c.variables ++ body.variables).contains := by
        simp only [List.mem_filter, List.contains_iff_mem]
        exact ⟨hplanActive, by simp [hbodyVar]⟩
      have hcond := whileCondOutputFuture (ec := .shrink profile context)
      change x ∈ (whileCondContext (.shrink profile context)).outputFuture
      rw [hcond]
      simp only [EvaluationContext.outputFuture]
      exact List.mem_append_left _ hbackedge
    · rcases List.mem_append.mp hrest with hbackedge | houter
      · have hbackedgeFuture := whileCondOutputFuture (ec := .shrink profile context)
        change x ∈ (whileCondContext (.shrink profile context)).outputFuture
        rw [hbackedgeFuture]
        simp only [EvaluationContext.outputFuture]
        exact List.mem_append_left _ hbackedge
      · have hbackedgeFuture := whileCondOutputFuture (ec := .shrink profile context)
        change x ∈ (whileCondContext (.shrink profile context)).outputFuture
        rw [hbackedgeFuture]
        simp only [EvaluationContext.outputFuture]
        exact List.mem_append_right _ houter

private theorem whileBodyOutput_coversInput {path : List Nat} {c : Expr} {body : Block}
    {origin : OriginId} {tenv : TEnv}
    (ec : EvaluationContext m plans path (.statement (.while c body origin)) .statement)
    (hactive : ec.ActiveMatches tenv) :
    ∀ x, x ∈ tenv.visible → x ∈ ec.inputFuture → x ∈ (whileBodyContext ec).outputFuture := by
  cases ec with
  | pilot profile active =>
    intro x hvisible _
    simpa [whileBodyContext, EvaluationContext.child, EvaluationContext.outputFuture,
      DemandNode.visibleForChild, DemandNode.visibleAfter] using (hactive x).2 hvisible
  | shrink profile context =>
    intro x hvisible hinput
    have hout := whileBodyOutputFuture (ec := .shrink profile context)
    change x ∈ (whileBodyContext (.shrink profile context)).outputFuture
    rw [hout]
    simp only [EvaluationContext.inputFuture, NodeContext.inputFuture,
      DemandNode.variables, Stmt.variables] at hinput
    simp only [EvaluationContext.outputFuture]
    apply List.mem_append.mpr
    rcases List.mem_append.mp hinput with hnode | hfuture
    · have hplanActive : x ∈ context.expected.frame.active := (hactive x).2 hvisible
      have hbackedge : x ∈ context.expected.frame.active.filter
          (c.variables ++ body.variables).contains := by
        simp only [List.mem_filter, List.contains_iff_mem]
        exact ⟨hplanActive, by simpa using hnode⟩
      exact Or.inl hbackedge
    · exact Or.inr hfuture

private theorem whileChildOutputs_eq {path : List Nat} {c : Expr} {body : Block} {origin : OriginId}
    (ec : EvaluationContext m plans path (.statement (.while c body origin)) .statement) :
    (whileCondContext ec).outputFuture = (whileBodyContext ec).outputFuture := by
  rw [whileCondOutputFuture, whileBodyOutputFuture]

private theorem whileCondOutput_coversInput {path : List Nat} {c : Expr} {body : Block}
    {origin : OriginId} {tenv : TEnv}
    (ec : EvaluationContext m plans path (.statement (.while c body origin)) .statement)
    (hactive : ec.ActiveMatches tenv) :
    ∀ x, x ∈ tenv.visible → x ∈ ec.inputFuture → x ∈ (whileCondContext ec).outputFuture := by
  intro x hvisible hinput
  rw [whileChildOutputs_eq]
  exact whileBodyOutput_coversInput ec hactive x hvisible hinput

private theorem whileOutput_subset_input {path : List Nat} {c : Expr} {body : Block} {origin : OriginId}
    (ec : EvaluationContext m plans path (.statement (.while c body origin)) .statement) :
    ∀ x, x ∈ ec.outputFuture → x ∈ ec.inputFuture := by
  cases ec with
  | pilot profile active =>
    intro x hx
    have hx' : x ∈ active := by
      simpa [EvaluationContext.outputFuture, DemandNode.visibleAfter] using hx
    have hfuture : x ∈ ((c.variables ++ body.variables) ++ active) :=
      List.mem_append_right _ hx'
    simpa [EvaluationContext.inputFuture, DemandNode.variables, Stmt.variables] using hfuture
  | shrink profile context =>
    intro x hx
    simp only [EvaluationContext.outputFuture, NodeContext.outputFuture] at hx
    simp only [EvaluationContext.inputFuture, NodeContext.inputFuture,
      DemandNode.variables, Stmt.variables]
    exact List.mem_append_right _ hx

private theorem rangeBodyOutputFuture {path : List Nat} {x : VarId} {lower upper : Expr}
    {body : Block} {origin : OriginId}
    (ec : EvaluationContext m plans path
      (.statement (.forRange x lower upper body origin)) .statement) :
    (rangeBodyContext ec).outputFuture = match ec with
      | .pilot _ active =>
        (DemandNode.statement (.forRange x lower upper body origin)).visibleForChild active 2
      | .shrink _ context =>
        (context.expected.frame.active.filter body.variables.contains) ++ context.expected.frame.future := by
  cases ec with
  | pilot profile active =>
    simp [rangeBodyContext, EvaluationContext.child, EvaluationContext.outputFuture,
      DemandNode.visibleAfter]
  | shrink profile context =>
    let transition := context.child (by simp [DemandNode.primaryPhase]) 2 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
    have hchild :
        (DemandNode.statement (.forRange x lower upper body origin)).childExpectation?
          ⟨context.expected.path, .expression, context.expected.frame.active,
            context.expected.frame.future, context.expected.frame.retained⟩ 2 = some
          ⟨(DemandNode.statement (.forRange x lower upper body origin)).visibleForChild
              context.expected.frame.active 2,
            (context.expected.frame.active.filter body.variables.contains) ++
              context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children,
        DemandNode.visibleForChild]
    have hfuture : transition.childFrame.future =
        (context.expected.frame.active.filter body.variables.contains) ++
          context.expected.frame.future := by
      have h := DemandNode.childFrame_future transition.childFrameEq hchild
      simpa [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children]
        using h
    change transition.context.expected.frame.future = _
    rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq, hfuture]

private theorem rangeBodyOutput_coversInput {path : List Nat} {x : VarId} {lower upper : Expr}
    {body : Block} {origin : OriginId} {tenv : TEnv}
    (ec : EvaluationContext m plans path
      (.statement (.forRange x lower upper body origin)) .statement)
    (hactive : ec.ActiveMatches tenv) :
    ∀ y, y ∈ tenv.visible → y ∈ body.variables ++ ec.outputFuture →
      y ∈ (rangeBodyContext ec).outputFuture := by
  cases ec with
  | pilot profile active =>
    intro y hvisible _
    have hmem : y ∈ active := (hactive y).2 hvisible
    change y ∈ (DemandNode.statement (.forRange x lower upper body origin)).visibleForChild active 2
    by_cases hx : x ∈ active <;> simp [DemandNode.visibleForChild, hx, hmem]
  | shrink profile context =>
    intro y hvisible hfuture
    have hactiveY : y ∈ context.expected.frame.active := (hactive y).2 hvisible
    change y ∈ body.variables ++ (EvaluationContext.shrink profile context).outputFuture at hfuture
    simp only [EvaluationContext.outputFuture] at hfuture
    change y ∈ (rangeBodyContext (.shrink profile context)).outputFuture
    rw [rangeBodyOutputFuture]
    simp only [EvaluationContext.outputFuture]
    rcases List.mem_append.mp hfuture with hbody | houter
    · apply List.mem_append_left
      simp only [List.mem_filter, List.contains_iff_mem]
      exact ⟨hactiveY, hbody⟩
    · exact List.mem_append_right _ houter

private theorem rangeBodyOutput_coversOutput {path : List Nat} {x : VarId} {lower upper : Expr}
    {body : Block} {origin : OriginId} {tenv : TEnv}
    (ec : EvaluationContext m plans path
      (.statement (.forRange x lower upper body origin)) .statement)
    (hactive : ec.ActiveMatches tenv) :
    ∀ y, y ∈ tenv.visible → y ∈ ec.outputFuture →
      y ∈ (rangeBodyContext ec).outputFuture := by
  intro y hvisible hfuture
  exact rangeBodyOutput_coversInput ec hactive y hvisible (List.mem_append_right _ hfuture)

private theorem rangeBodyOutput_subsetInput {path : List Nat} {x : VarId} {lower upper : Expr}
    {body : Block} {origin : OriginId} {tenv : TEnv}
    (ec : EvaluationContext m plans path
      (.statement (.forRange x lower upper body origin)) .statement)
    (hactive : ec.ActiveMatches tenv) :
    ∀ y, y ∈ tenv.visible → y ∈ (rangeBodyContext ec).outputFuture →
      y ∈ body.variables ++ ec.outputFuture := by
  cases ec with
  | pilot profile active =>
    intro y hvisible _
    exact List.mem_append_right _ ((hactive y).2 hvisible)
  | shrink profile context =>
    intro y hvisible hfuture
    have hactiveY : y ∈ context.expected.frame.active := (hactive y).2 hvisible
    change y ∈ (rangeBodyContext (.shrink profile context)).outputFuture at hfuture
    rw [rangeBodyOutputFuture] at hfuture
    simp only [EvaluationContext.outputFuture]
    rcases List.mem_append.mp hfuture with hbody | houter
    · simp only [List.mem_filter, List.contains_iff_mem] at hbody
      have hbodyMem : y ∈ body.variables := hbody.2
      exact List.mem_append_left _ hbodyMem
    · exact List.mem_append_right _ houter

private theorem retOk_tenv_congr {m : Module} {W : World} {tenv tenv' : TEnv}
    {penv penv' : PEnv} {s : St} {v : Val}
    (h : RetOk m W tenv' penv' s v) (htenv : tenv'.impl = tenv.impl)
    (hpenv : penv'.ctx = penv.ctx) : RetOk m W tenv penv s v := by
  obtain ⟨impl, himpl, hresult, htargets⟩ := h
  exact ⟨impl, htenv ▸ himpl, hresult, hpenv ▸ htargets⟩

set_option maxHeartbeats 800000 in
theorem step_while (ih : Specs m prof plans n) : WhileSpec m prof plans (n + 1) := by
  intro path c body origin ec observation W tenv penv env s tn tn1 tn2 bty rst rst1 rst2 rhoc rb rng
    hactive haccess hprotected hobserved hp hF htc htb hrc hrb hE
  let conditionEc := whileCondContext ec
  let bodyEc := whileBodyContext ec
  let loopT := { tenv with loops := tenv.loops + 1 }
  have hactiveCondition : conditionEc.ActiveMatches tenv :=
    ec.child_activeMatches (by simp [DemandNode.primaryPhase]) 0 (.expression c) .expression
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) tenv tenv hactive
      (by intro x; simp [DemandNode.visibleForChild])
  have hactiveBody : bodyEc.ActiveMatches loopT :=
    ec.child_activeMatches (by simp [DemandNode.primaryPhase]) 1 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) tenv loopT hactive
      (by intro x; simp [loopT, DemandNode.visibleForChild])
  have haccessLoop : ec.AccessMatches loopT penv := by
    simpa [EvaluationContext.AccessMatches, NodeContext.AccessMatches, loopT] using haccess
  have haccessCondition : conditionEc.AccessMatches tenv penv :=
    (ec.child_accessMatches_iff (by simp [DemandNode.primaryPhase]) 0 (.expression c) .expression
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) tenv penv).2 haccess
  have haccessBody : bodyEc.AccessMatches loopT penv :=
    (ec.child_accessMatches_iff (by simp [DemandNode.primaryPhase]) 1 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) loopT penv).2 haccessLoop
  have hmayCondition : ∀ r, conditionEc.mayShrink W.P r ↔ ec.mayShrink W.P r := by
    intro r
    exact ec.child_mayShrink_iff (by simp [DemandNode.primaryPhase]) 0 (.expression c) .expression
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) W.P r
  have hmayBody : ∀ r, bodyEc.mayShrink W.P r ↔ ec.mayShrink W.P r := by
    intro r
    exact ec.child_mayShrink_iff (by simp [DemandNode.primaryPhase]) 1 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) W.P r
  have hprotectedCondition : ShrinkProtected W.D W.A (conditionEc.mayShrink W.P) :=
    ShrinkProtected.mono hprotected (fun _ _ h => h) (fun _ _ h => h)
      (fun r h => (hmayCondition r).1 h)
  have hprotectedBody : ShrinkProtected W.D W.A (bodyEc.mayShrink W.P) :=
    ShrinkProtected.mono hprotected (fun _ _ h => h) (fun _ _ h => h)
      (fun r h => (hmayBody r).1 h)
  have hobservedCondition : ObservedSafe m W (conditionEc.mayShrink W.P) observation s.store :=
    hobserved.weakenShrinking (fun r h => (hmayCondition r).1 h)
  have hobservedBody : ObservedSafe m W (bodyEc.mayShrink W.P) observation s.store :=
    hobserved.weakenShrinking (fun r h => (hmayBody r).1 h)
  have hFCondition : Frame m W tenv penv env s conditionEc.inputFuture :=
    hF.narrowFuture (whileCondInput_subset ec)
  have hFLoop : Frame m W loopT penv env s ec.inputFuture :=
    hF.tenv_congr rfl rfl rfl (fun _ h => h)
  have hFBody : Frame m W loopT penv env s bodyEc.inputFuture :=
    hFLoop.narrowFuture (whileBodyInput_subset ec)
  have hBodyActiveAfterDeclare : ∀ env1 tnEnd,
      declarePre { loopT with scopes := body.scope :: loopT.scopes } body.scope [] tn1 =
        .ok (env1, tnEnd) → bodyEc.ActiveMatches env1 := by
    intro env1 tnEnd hdeclare
    obtain ⟨_, hvis, _, _⟩ := declarePre_ok _ _ _ _ _ _ hdeclare
    have hvisible : ∀ x, x ∈ env1.visible ↔ x ∈ tenv.visible := by
      intro x
      simpa [loopT] using hvis x
    exact ec.child_activeMatches (by simp [DemandNode.primaryPhase]) 1 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) tenv env1 hactive
      (by intro x; simpa [DemandNode.visibleForChild] using hvisible x)
  have body_part : ∀ (s1 : St), Frame m W loopT penv env s1 bodyEc.inputFuture →
      Footprint (insts env) (Dset W) s s1 →
      PreservesRootTypes m W.G observation.roots s.store s1.store →
      PreservesValues m W.G observation.values s.store s1.store →
      ObservedSafe m W (ec.mayShrink W.P) observation s1.store →
      RetainsAliases m W env s.store s1.store ec.retained →
      PilotStoreLe m s s1 →
      Sat (execBlock n ⟨prof, m⟩ env [] body >>= fun fl =>
        match fl with
        | .normal _ => execWhile n ⟨prof, m⟩ env c body
        | .cont => execWhile n ⟨prof, m⟩ env c body
        | .brk => pure (.normal .unit)
        | .ret v => pure (.ret v)) s1 (fun fl s' =>
        Frame m W tenv penv env s' ec.outputFuture ∧
        Footprint (insts env) (Dset W) s s' ∧
        PreservesRootTypes m W.G observation.roots s.store s'.store ∧
        PreservesValues m W.G observation.values s.store s'.store ∧
        ObservedSafe m W (ec.mayShrink W.P) observation s'.store ∧
        RetainsAliases m W env s.store s'.store ec.retained ∧
        PilotStoreLe m s s' ∧ LoopFlow m W tenv penv s' fl ∧
        (∀ v, fl = .normal v → c = .bool true → body.hasBreak = true)) := by
    intro s1 hF1 hFoot1 hRoots1 hValues1 hSafe1 hRetained1 hPilot1
    have hSafeBody1 : ObservedSafe m W (bodyEc.mayShrink W.P) observation s1.store :=
      hSafe1.weakenShrinking (fun r h => (hmayBody r).1 h)
    refine Sat.bind (block_of_checks ih.block hp body bodyEc observation [] []
      hBodyActiveAfterDeclare haccessBody hprotectedBody hSafeBody1 hF1 htb hrb hE rfl rfl
      (fun _ _ _ _ h => by simp at h)) ?_
    rintro fl s2 ⟨hF2, hFoot2, hRoots2, hValues2, hSafe2, hRetained2, hPilot2, hFlow⟩
    have hSafe2Parent : ObservedSafe m W (ec.mayShrink W.P) observation s2.store :=
      hSafe2.weakenShrinking (fun r h => (hmayBody r).2 h)
    have hRetained2Parent : RetainsAliases m W env s1.store s2.store ec.retained :=
      hRetained2.subset (fun alias hmem =>
        ec.child_retained_subset (by simp [DemandNode.primaryPhase]) 1 (.block body) .block
          (by simp [DemandNode.child?, DemandNode.children])
          (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) hmem)
    have hF2Outer : Frame m W tenv penv env s2 bodyEc.outputFuture :=
      hF2.tenv_congr rfl rfl rfl (fun _ h => h)
    have hF2LoopInput : Frame m W tenv penv env s2 ec.inputFuture :=
      hF2Outer.changeFuture (fun x hvisible hfuture =>
        whileBodyOutput_coversInput ec hactive x hvisible hfuture)
    have hF2LoopOutput : Frame m W tenv penv env s2 ec.outputFuture :=
      hF2Outer.changeFuture (fun x hvisible hfuture =>
        whileBodyOutput_coversInput ec hactive x hvisible
          (whileOutput_subset_input ec x hfuture))
    have hFoot2Start := hFoot1.trans hFoot2
    have hRoots2Start := hRoots1.trans hRoots2
    have hValues2Start := hValues1.trans hValues2
    have hRetained2Start := hRetained1.trans hRetained2Parent
    have hPilot2Start : PilotStoreLe m s s2 := by
      intro hpilot
      exact (hPilot1 hpilot).trans (hPilot2 hpilot)
    cases fl with
    | normal v =>
      have hAgain := ih.while_ path c body origin ec observation W tenv penv env s2 tn tn1 tn2 bty
        rst rst1 rst2 rhoc rb rng hactive haccess hprotected hSafe2Parent hp hF2LoopInput
        htc htb hrc hrb hE
      exact hAgain.mono (fun fl3 s3 ⟨hF3, hFoot3, hRoots3, hValues3, hSafe3, hRetained3,
          hPilot3, hFlow3, hBreak3⟩ =>
        ⟨hF3, hFoot2Start.trans hFoot3, hRoots2Start.trans hRoots3,
          hValues2Start.trans hValues3, hSafe3, hRetained2Start.trans hRetained3,
          (fun hpilot => (hPilot2Start hpilot).trans (hPilot3 hpilot)), hFlow3, hBreak3⟩)
    | cont =>
      have hAgain := ih.while_ path c body origin ec observation W tenv penv env s2 tn tn1 tn2 bty
        rst rst1 rst2 rhoc rb rng hactive haccess hprotected hSafe2Parent hp hF2LoopInput
        htc htb hrc hrb hE
      exact hAgain.mono (fun fl3 s3 ⟨hF3, hFoot3, hRoots3, hValues3, hSafe3, hRetained3,
          hPilot3, hFlow3, hBreak3⟩ =>
        ⟨hF3, hFoot2Start.trans hFoot3, hRoots2Start.trans hRoots3,
          hValues2Start.trans hValues3, hSafe3, hRetained2Start.trans hRetained3,
          (fun hpilot => (hPilot2Start hpilot).trans (hPilot3 hpilot)), hFlow3, hBreak3⟩)
    | brk =>
      simp only [sat_pure]
      exact ⟨hF2LoopOutput, hFoot2Start, hRoots2Start, hValues2Start, hSafe2Parent,
        hRetained2Start, hPilot2Start, trivial, fun _ _ _ => hFlow.2⟩
    | ret v =>
      simp only [sat_pure]
      exact ⟨hF2LoopOutput, hFoot2Start, hRoots2Start, hValues2Start, hSafe2Parent,
        hRetained2Start, hPilot2Start, ⟨hFlow.1, retOk_tenv_congr hFlow.2 rfl rfl⟩,
        fun v' h => by cases h⟩
  by_cases hc : c = .bool true
  · subst hc
    rw [execWhile, evalExpr_bool]
    by_cases hn : n = 0
    · rw [if_pos hn]; exact trivial
    · rw [if_neg hn]
      exact body_part s hFBody (Footprint.refl (insts env) (Dset W) s)
        (PreservesRootTypes.refl s.store) (PreservesValues.refl s.store) hobserved
        RetainsAliases.refl (by intro _; exact StoreLe.refl _)
  · simp only [execWhile]
    refine Sat.bind (ih.expr (path ++ [0]) c conditionEc observation W tenv penv env s tn tn1 .bool
      rst rst1 rhoc hactiveCondition haccessCondition hprotectedCondition hobservedCondition hp hFCondition
      htc hrc
      ((rpBlockValue_mono hrb).2.trans hE)) ?_
    rintro vc s1 ⟨hF1, hFoot1, hRoots1, hValues1, hSafe1, hRetained1, hPilot1, hv, _⟩
    obtain ⟨x, rfl⟩ := hasTy_bool hv
    have hSafe1Parent : ObservedSafe m W (ec.mayShrink W.P) observation s1.store :=
      hSafe1.weakenShrinking (fun r h => (hmayCondition r).2 h)
    have hRetained1Parent : RetainsAliases m W env s.store s1.store ec.retained :=
      hRetained1.subset (fun alias hmem =>
        ec.child_retained_subset (by simp [DemandNode.primaryPhase]) 0 (.expression c) .expression
          (by simp [DemandNode.child?, DemandNode.children])
          (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) hmem)
    have hF1Loop : Frame m W loopT penv env s1 conditionEc.outputFuture :=
      hF1.tenv_congr rfl rfl rfl (fun _ h => h)
    have hF1Body : Frame m W loopT penv env s1 bodyEc.inputFuture :=
      hF1Loop.changeFuture (fun x hvisible hfuture =>
        whileCondOutput_coversBodyInput ec hactive x (by simpa [loopT] using hvisible) hfuture)
    simp only [expectBool, sat_pure_bind]
    cases x
    · simp only [Bool.false_eq_true, if_false, sat_pure]
      have hF1Output : Frame m W tenv penv env s1 ec.outputFuture :=
        hF1.changeFuture (fun x hvisible hfuture =>
          whileCondOutput_coversInput ec hactive x hvisible (whileOutput_subset_input ec x hfuture))
      exact ⟨hF1Output, hFoot1, hRoots1, hValues1, hSafe1Parent, hRetained1Parent,
        hPilot1, trivial, fun _ _ h => absurd h hc⟩
    · simp only [if_true]
      exact body_part s1 hF1Body hFoot1 hRoots1 hValues1 hSafe1Parent hRetained1Parent hPilot1

set_option maxHeartbeats 800000 in
theorem step_range (ih : Specs m prof plans n) : RangeSpec m prof plans (n + 1) := by
  intro path x lower upper body origin ec observation W tenv penv env s t i hi tn1 tn2 bty rst1 rst2 rb rng
    hactive haccess hprotected hobserved hp hF hx hlt htb hrb hE hk0
  let bodyEc := rangeBodyContext ec
  let loopT := { tenv with loops := tenv.loops + 1 }
  have hactiveLoop : ec.ActiveMatches loopT := by
    simpa [EvaluationContext.ActiveMatches, NodeContext.ActiveMatches, loopT] using hactive
  have haccessLoop : ec.AccessMatches loopT penv := by
    simpa [EvaluationContext.AccessMatches, NodeContext.AccessMatches, loopT] using haccess
  have haccessBody : bodyEc.AccessMatches loopT penv :=
    (ec.child_accessMatches_iff (by simp [DemandNode.primaryPhase]) 2 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) loopT penv).2 haccessLoop
  have hmayBody : ∀ r, bodyEc.mayShrink W.P r ↔ ec.mayShrink W.P r := by
    intro r
    exact ec.child_mayShrink_iff (by simp [DemandNode.primaryPhase]) 2 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) W.P r
  have hprotectedBody : ShrinkProtected W.D W.A (bodyEc.mayShrink W.P) :=
    ShrinkProtected.mono hprotected (fun _ _ h => h) (fun _ _ h => h)
      (fun r h => (hmayBody r).1 h)
  have hobservedBody : ObservedSafe m W (bodyEc.mayShrink W.P) observation s.store :=
    hobserved.weakenShrinking (fun r h => (hmayBody r).1 h)
  have hFLoop : Frame m W loopT penv env s (body.variables ++ ec.outputFuture) :=
    hF.tenv_congr rfl rfl rfl (fun _ h => h)
  have hFBody : Frame m W loopT penv env s bodyEc.inputFuture := by
    have hInputFuture : bodyEc.inputFuture = body.variables ++ bodyEc.outputFuture := by
      cases ec <;> rfl
    rw [hInputFuture]
    exact hFLoop.changeFuture (fun y hvisible hfuture => by
      rcases List.mem_append.mp hfuture with hbody | houter
      · exact List.mem_append_left _ hbody
      · exact rangeBodyOutput_subsetInput ec hactive y hvisible houter)
  have hBodyActiveAfterDeclare : ∀ env1 tnEnd,
      declarePre { {loopT with visible := x :: loopT.visible} with scopes := body.scope :: loopT.scopes }
          body.scope [] tn1 = .ok (env1, tnEnd) → bodyEc.ActiveMatches env1 := by
    intro env1 tnEnd hdeclare
    obtain ⟨_, hvis, _, _⟩ := declarePre_ok _ _ _ _ _ _ hdeclare
    have hvisible : ∀ y, y ∈ env1.visible ↔ y ∈ x :: tenv.visible := by
      intro y
      simpa [loopT] using hvis y
    exact ec.child_activeMatches (by simp [DemandNode.primaryPhase]) 2 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) tenv env1 hactive
      (by
        intro y
        rw [hvisible y]
        by_cases hx : x ∈ tenv.visible
        · have hcons : y ∈ x :: tenv.visible ↔ y ∈ tenv.visible := by
            constructor
            · intro hmem
              rcases List.mem_cons.mp hmem with heq | hmem
              · simpa [heq] using hx
              · exact hmem
            · intro hmem
              exact List.mem_cons.mpr (Or.inr hmem)
          simpa [DemandNode.visibleForChild, hx] using hcons
        · simp [DemandNode.visibleForChild, hx])
  simp only [execRange]
  by_cases h : i < hi
  · simp only [h, if_true]
    obtain ⟨lv, hlv, hsc, hty⟩ := hx
    refine Sat.bind (block_of_reserved ih.block hp body bodyEc observation [(x, .int t i)] [x] x
      hBodyActiveAfterDeclare haccessBody hprotectedBody hobservedBody hFBody htb hrb hE
      rfl (by simp) ?_ (Nat.le_of_lt hlt) hk0) ?_
    · intro x' v hm
      simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      refine ⟨Nat.le_refl _, hlt, lv, hlv, hsc, by rw [hty]; rfl, ?_, fun r hr => hr.elim⟩
      rw [hty]
      exact hasTy_of_flat (T := .int t) (show FlatTy (.int t) (.int t i) from rfl) (Or.inl rfl)
    · rintro fl s2 ⟨hF2, hFoot2, hRoots2, hValues2, hSafe2, hRetained2, hPilot2, hFlow⟩
      have hSafe2Parent : ObservedSafe m W (ec.mayShrink W.P) observation s2.store :=
        hSafe2.weakenShrinking (fun r h => (hmayBody r).2 h)
      have hRetained2Parent : RetainsAliases m W env s.store s2.store ec.retained :=
        hRetained2.subset (fun alias hmem =>
          ec.child_retained_subset (by simp [DemandNode.primaryPhase]) 2 (.block body) .block
            (by simp [DemandNode.child?, DemandNode.children])
            (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) hmem)
      have hF2LoopInput : Frame m W tenv penv env s2 (body.variables ++ ec.outputFuture) := by
        have hF2Loop : Frame m W loopT penv env s2 (body.variables ++ ec.outputFuture) :=
          hF2.changeFuture (fun y hvisible hfuture => by
            rcases List.mem_append.mp hfuture with hbody | houter
            · exact rangeBodyOutput_coversInput ec hactive y hvisible (List.mem_append_left _ hbody)
            · exact rangeBodyOutput_coversInput ec hactive y hvisible (List.mem_append_right _ houter))
        exact hF2Loop.tenv_congr rfl rfl rfl (fun _ h => h)
      have hF2LoopOutput : Frame m W tenv penv env s2 ec.outputFuture := by
        have hF2Loop : Frame m W loopT penv env s2 ec.outputFuture :=
          hF2.changeFuture (rangeBodyOutput_coversOutput ec hactive)
        exact hF2Loop.tenv_congr rfl rfl rfl (fun _ h => h)
      cases fl with
      | normal v =>
        have hAgain := ih.range path x lower upper body origin ec observation W tenv penv env s2 t
          (i + 1) hi tn1 tn2 bty rst1 rst2 rb rng hactive haccess hprotected hSafe2Parent hp
          hF2LoopInput ⟨lv, hlv, hsc, hty⟩ hlt htb hrb hE hk0
        exact hAgain.mono (fun fl3 s3
          ⟨hF3, hFoot3, hRoots3, hValues3, hSafe3, hRetained3, hPilot3, hFlow3⟩ =>
            ⟨hF3, hFoot2.trans hFoot3, hRoots2.trans hRoots3, hValues2.trans hValues3,
              hSafe3, hRetained2Parent.trans hRetained3,
              (fun hpilot => (hPilot2 hpilot).trans (hPilot3 hpilot)), hFlow3⟩)
      | cont =>
        have hAgain := ih.range path x lower upper body origin ec observation W tenv penv env s2 t
          (i + 1) hi tn1 tn2 bty rst1 rst2 rb rng hactive haccess hprotected hSafe2Parent hp
          hF2LoopInput ⟨lv, hlv, hsc, hty⟩ hlt htb hrb hE hk0
        exact hAgain.mono (fun fl3 s3
          ⟨hF3, hFoot3, hRoots3, hValues3, hSafe3, hRetained3, hPilot3, hFlow3⟩ =>
            ⟨hF3, hFoot2.trans hFoot3, hRoots2.trans hRoots3, hValues2.trans hValues3,
              hSafe3, hRetained2Parent.trans hRetained3,
              (fun hpilot => (hPilot2 hpilot).trans (hPilot3 hpilot)), hFlow3⟩)
      | brk =>
        simp only [sat_pure]
        exact ⟨hF2LoopOutput, hFoot2, hRoots2, hValues2, hSafe2Parent, hRetained2Parent,
          hPilot2, trivial⟩
      | ret v =>
        simp only [sat_pure]
        exact ⟨hF2LoopOutput, hFoot2, hRoots2, hValues2, hSafe2Parent, hRetained2Parent,
          hPilot2, ⟨hFlow.1, retOk_tenv_congr hFlow.2 rfl rfl⟩⟩
  · simp only [h, if_false, sat_pure]
    exact ⟨hF.narrowFuture (fun _ h => List.mem_append_right _ h),
      Footprint.refl (insts env) (Dset W) s, PreservesRootTypes.refl s.store,
      PreservesValues.refl s.store, hobserved, RetainsAliases.refl,
      (fun _ => StoreLe.refl _), trivial⟩

set_option maxHeartbeats 1600000 in
theorem step_each (ih : Specs m prof plans n) : EachSpec m prof plans (n + 1) := by
  intro path x idx sourceView byRef body origin ec observation W tenv penv env s vw i el rho
    tn1 tn2 bty rst1 rst2 rb rng hactive haccess hprotected hobserved hp hF hvw hViewAliases hg
    hx hj hlt htb hrb hE hk0
  rw [execEach_eq]
  refine Sat.bind (R := fun len s' => s' = s ∧ SliceTy s.store vw.loc vw.start len el) ?_ ?_
  · cases hres : vw.resizable with
    | false =>
      rw [if_neg Bool.false_ne_true]
      exact ⟨rfl, hvw.2.1 hres⟩
    | true =>
      rw [if_pos rfl]
      obtain ⟨hst, hlt'⟩ := hvw.2.2 hres
      rcases hlt' with hgrow | hgrowshrink
      · refine sat_lengthLoc hgrow (fun es hread => ⟨rfl, ?_⟩)
        rw [hst]
        exact sliceTy_of_grow hgrow hread
      · refine sat_lengthLoc_growshrink hgrowshrink (fun es hread => ⟨rfl, ?_⟩)
        rw [hst]
        exact sliceTy_of_growshrink hgrowshrink hread
  · rintro len s' ⟨rfl, hsl⟩
    by_cases h : i < len
    · simp only [h, if_true]
      have hel : LocTy s'.store ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩ el := sliceTy_elem hsl h
      have hFl : Frame m W { tenv with loops := tenv.loops + 1 } penv env s' :=
        hF.tenv_congr rfl rfl rfl (fun _ h => h)
      obtain ⟨lv, hlv, hsc, hst, hxty⟩ := hx
      have hxlt : x < rst1.nextVar := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlt
      have hnd : (x :: idx.toList).Nodup := by
        cases idx with
        | none => simp
        | some j =>
          have hjx := (hj j rfl).1
          simp only [Option.toList_some, List.nodup_cons, List.mem_singleton, List.not_mem_nil,
            not_false_eq_true, List.nodup_nil, and_true]
          intro e
          rw [← e] at hjx
          exact absurd hjx (Nat.ne_of_lt (Nat.lt_succ_self x))
      -- The rest of an iteration, for the value the loop variable gets.
      have rest : ∀ (ev : Val) (pre' : List (VarId × Val)), pre' = idxVal i idx →
          (HasTy m W.G s'.store ev lv.ty ∧ ∀ r, Targets ev r → ∃ ann, penv.ann x = some ann ∧
              Gam env W.P ann r) →
          Sat (execBlock n ⟨prof, m⟩ env ((x, ev) :: pre') body >>= fun fl =>
            match fl with
            | .normal _ => execEach n ⟨prof, m⟩ env x idx byRef body vw (i + 1)
            | .cont => execEach n ⟨prof, m⟩ env x idx byRef body vw (i + 1)
            | .brk => pure (.normal .unit)
            | .ret v => pure (.ret v)) s' (fun fl s2 =>
            Frame m W tenv penv env s2 ∧ Ext (insts env) (Dset W) s' s2 ∧
              LoopFlow m W tenv penv s2 fl) := by
        intro ev pre' hpre' hev
        subst hpre'
        refine Sat.bind (block_of_reserved ih.block hp hFl body ((x, ev) :: idxVal i idx)
          (x :: idx.toList) x htb hrb hE (by cases idx <;> rfl) hnd ?_ (Nat.le_of_lt hxlt) hk0) ?_
        · intro x' v hm
          rcases List.mem_cons.1 hm with e | hm
          · cases e
            exact ⟨Nat.le_refl _, hxlt, lv, hlv, hsc, paramOk_of_storable hst, hev.1, hev.2⟩
          · cases idx with
            | none => simp [idxVal] at hm
            | some j =>
              simp only [idxVal, List.mem_singleton, Prod.mk.injEq] at hm
              obtain ⟨rfl, rfl⟩ := hm
              obtain ⟨hjx, lj, hlj, hljsc, hljty⟩ := hj _ rfl
              refine ⟨by rw [hjx]; exact Nat.le_succ _, by rw [hjx]; simpa using hlt, lj, hlj, hljsc,
                by rw [hljty]; rfl, ?_, fun r hr => hr.elim⟩
              rw [hljty]
              exact hasTy_of_flat (T := .int .i64) (show FlatTy (.int .i64) (.int .i64 i) from rfl)
                (Or.inl rfl)
        · rintro fl s2 ⟨hF2, hX2, hfl⟩
          have hF2' : Frame m W tenv penv env s2 := hF2.tenv_congr rfl rfl rfl (fun _ h => h)
          have again := (ih.each W tenv penv env s2 x idx byRef body vw (i + 1) el rho tn1 tn2 bty
            rst1 rst2 rb rng hp hF2' (hvw.mono hX2.le) hg ⟨lv, hlv, hsc, hst, hxty⟩ hj hlt htb hrb hE
            hk0).mono (Q := fun fl s3 =>
              Frame m W tenv penv env s3 ∧ Ext (insts env) (Dset W) s' s3 ∧
                LoopFlow m W tenv penv s3 fl)
            (fun fl s3 ⟨g1, g2, g3⟩ => ⟨g1, hX2.trans g2, g3⟩)
          cases fl with
          | normal v => exact again
          | cont => exact again
          | brk =>
            simp only [sat_pure]
            exact ⟨hF2', hX2, trivial⟩
          | ret v =>
            simp only [sat_pure]
            exact ⟨hF2', hX2, hfl.1, hfl.2.tsame rfl rfl⟩
      cases byRef with
      | true =>
        simp only [if_true, sat_pure_bind]
        rw [if_pos rfl] at hxty
        obtain ⟨⟨mx, hty⟩, hbr⟩ := hxty
        refine rest _ _ (by cases idx <;> rfl) ⟨?_, fun r hr => ?_⟩
        · rw [hty]
          exact ⟨_, rfl, Or.inl ⟨flat_refTarget hvw.1, Or.inl hel, HeaderLoc.ofFlat hvw.1⟩⟩
        · cases hr
          obtain ⟨lv', ann, _, ha, hsub, _⟩ := bindRootsV_ok _ _ _ _ hbr
          exact ⟨ann, ha, hg.subset hsub⟩
      | false =>
        simp only [Bool.false_eq_true, if_false]
        have hty : lv.ty = el := by simpa using hxty
        refine sat_readLoc_bind hel (fun ev _ hT => ?_)
        refine rest _ _ (by cases idx <;> rfl) ⟨?_, flat_no_targets hT⟩
        rw [hty]
        exact hasTy_of_flat hT (Or.inl hvw.1)
    · simp only [h, if_false, sat_pure]
      exact ⟨hF, Ext.refl _ _ _, trivial⟩

end Goose.Core.Sound
