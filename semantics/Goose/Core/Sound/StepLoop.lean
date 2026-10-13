import Goose.Core.Sound.StepUse
import Goose.Core.Sound.RetainSyntax

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
  exact match ec with
  | .pilot profile active => by
    simp [whileCondContext, EvaluationContext.child, EvaluationContext.outputFuture,
      DemandNode.visibleForChild, DemandNode.visibleAfter]
  | .shrink (pc := pc) profile context => by
    let transition := context.child (by simp [DemandNode.primaryPhase]) 0 (.expression c) .expression
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
    have hchild :
        (DemandNode.statement (.while c body origin)).childExpectation?
          pc.approvals.access
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
  exact match ec with
  | .pilot profile active => by
    simp [whileBodyContext, EvaluationContext.child, EvaluationContext.outputFuture,
      DemandNode.visibleForChild, DemandNode.visibleAfter]
  | .shrink (pc := pc) profile context => by
    let transition := context.child (by simp [DemandNode.primaryPhase]) 1 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
    have hchild :
        (DemandNode.statement (.while c body origin)).childExpectation?
          pc.approvals.access
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
  exact match ec with
  | .pilot profile active => by
    simp [rangeBodyContext, EvaluationContext.child, EvaluationContext.outputFuture,
      DemandNode.visibleAfter]
  | .shrink (pc := pc) profile context => by
    let transition := context.child (by simp [DemandNode.primaryPhase]) 2 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
    have hchild :
        (DemandNode.statement (.forRange x lower upper body origin)).childExpectation?
          pc.approvals.access
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

private theorem eachBodyOutputFuture {path : List Nat} {x : VarId} {idx : Option VarId}
    {sourceView : View} {byRef : Bool} {body : Block} {origin : OriginId}
    (ec : EvaluationContext m plans path
      (.statement (.forEach x idx sourceView byRef body origin)) .statement) :
    (eachBodyContext ec).outputFuture = match ec with
      | .pilot _ active =>
        (DemandNode.statement (.forEach x idx sourceView byRef body origin)).visibleForChild active 1
      | .shrink _ context =>
        (context.expected.frame.active.filter body.variables.contains) ++
          context.expected.frame.future := by
  exact match ec with
  | .pilot profile active => by
    simp [eachBodyContext, EvaluationContext.child, EvaluationContext.outputFuture,
      DemandNode.visibleAfter]
  | .shrink (pc := pc) profile context => by
    let transition := context.child (by simp [DemandNode.primaryPhase]) 1 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
    have hchild :
        (DemandNode.statement (.forEach x idx sourceView byRef body origin)).childExpectation?
          pc.approvals.access
          ⟨context.expected.path, .expression, context.expected.frame.active,
            context.expected.frame.future, context.expected.frame.retained⟩ 1 = some
          ⟨(DemandNode.statement (.forEach x idx sourceView byRef body origin)).visibleForChild
              context.expected.frame.active 1,
            (context.expected.frame.active.filter body.variables.contains) ++
              context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?,
        DemandNode.children, DemandNode.visibleForChild]
    have hfuture : transition.childFrame.future =
        (context.expected.frame.active.filter body.variables.contains) ++
          context.expected.frame.future := by
      have h := DemandNode.childFrame_future transition.childFrameEq hchild
      simpa [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?,
        DemandNode.children] using h
    change transition.context.expected.frame.future = _
    rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq, hfuture]

private theorem foldVisibleMem {binders active : List VarId} {y : VarId} :
    y ∈ binders.foldl (fun active binder =>
      if active.contains binder then active else binder :: active) active ↔
      y ∈ binders ∨ y ∈ active := by
  induction binders generalizing active with
  | nil => simp
  | cons binder rest ih =>
    rw [List.foldl_cons]
    cases hcontains : active.contains binder with
    | true =>
      simp only [hcontains, if_pos]
      have hbinder : binder ∈ active := List.contains_iff_mem.mp hcontains
      rw [ih]
      simp only [List.mem_cons]
      constructor
      · intro hmem
        rcases hmem with hrest | hactive
        · exact Or.inl (Or.inr hrest)
        · exact Or.inr hactive
      · intro hmem
        rcases hmem with hmem | hactive
        · rcases hmem with heq | hrest
          · subst y
            exact Or.inr hbinder
          · exact Or.inl hrest
        · exact Or.inr hactive
    | false =>
      simp only [hcontains, Bool.false_eq_true, if_false]
      rw [ih (active := binder :: active)]
      simp only [List.mem_cons]
      constructor
      · intro hmem
        rcases hmem with hrest | heq | hactive
        · exact Or.inl (Or.inr hrest)
        · exact Or.inl (Or.inl heq)
        · exact Or.inr hactive
      · intro hmem
        rcases hmem with hmem | hactive
        · rcases hmem with heq | hrest
          · exact Or.inr (Or.inl heq)
          · exact Or.inl hrest
        · exact Or.inr (Or.inr hactive)

private theorem foldVisibleIff {binders active : List VarId} {y : VarId} :
    y ∈ binders.foldl (fun active binder =>
      if active.contains binder then active else binder :: active) active ↔
      y ∈ binders ++ active := by
  rw [List.mem_append]
  exact foldVisibleMem

private theorem foldVisibleContains {binders active : List VarId} {y : VarId}
    (h : y ∈ active) :
    y ∈ binders.foldl (fun active binder =>
      if active.contains binder then active else binder :: active) active :=
  foldVisibleIff.mpr (List.mem_append_right _ h)

private theorem eachBodyOutput_coversInput {path : List Nat} {x : VarId} {idx : Option VarId}
    {sourceView : View} {byRef : Bool} {body : Block} {origin : OriginId} {tenv : TEnv}
    (ec : EvaluationContext m plans path
      (.statement (.forEach x idx sourceView byRef body origin)) .statement)
    (hactive : ec.ActiveMatches tenv) :
    ∀ y, y ∈ tenv.visible → y ∈ body.variables ++ ec.outputFuture →
      y ∈ (eachBodyContext ec).outputFuture := by
  intro y hvisible hinput
  cases ec with
  | pilot profile active =>
    have hy : y ∈ active := (hactive y).2 hvisible
    change y ∈ (DemandNode.statement (.forEach x idx sourceView byRef body origin)).visibleForChild
      active 1
    unfold DemandNode.visibleForChild
    exact foldVisibleContains hy
  | shrink profile context =>
    have hactiveY : y ∈ context.expected.frame.active := (hactive y).2 hvisible
    change y ∈ body.variables ++ context.expected.frame.future at hinput
    change y ∈ (eachBodyContext (.shrink profile context)).outputFuture
    rw [eachBodyOutputFuture]
    rcases List.mem_append.mp hinput with hbody | houter
    · apply List.mem_append_left
      simp only [List.mem_filter, List.contains_iff_mem]
      exact ⟨hactiveY, hbody⟩
    · exact List.mem_append_right _ houter

private theorem eachBodyOutput_coversOutput {path : List Nat} {x : VarId} {idx : Option VarId}
    {sourceView : View} {byRef : Bool} {body : Block} {origin : OriginId} {tenv : TEnv}
    (ec : EvaluationContext m plans path
      (.statement (.forEach x idx sourceView byRef body origin)) .statement)
    (hactive : ec.ActiveMatches tenv) :
    ∀ y, y ∈ tenv.visible → y ∈ ec.outputFuture → y ∈ (eachBodyContext ec).outputFuture := by
  intro y hvisible hfuture
  exact eachBodyOutput_coversInput ec hactive y hvisible (List.mem_append_right _ hfuture)

private theorem eachBodyOutput_subsetInput {path : List Nat} {x : VarId} {idx : Option VarId}
    {sourceView : View} {byRef : Bool} {body : Block} {origin : OriginId} {tenv : TEnv}
    (ec : EvaluationContext m plans path
      (.statement (.forEach x idx sourceView byRef body origin)) .statement)
    (hactive : ec.ActiveMatches tenv) :
    ∀ y, y ∈ tenv.visible → y ∈ (eachBodyContext ec).outputFuture →
      y ∈ body.variables ++ ec.outputFuture := by
  cases ec with
  | pilot profile active =>
    intro y hvisible hfuture
    have hy : y ∈ active := (hactive y).2 hvisible
    simp only [EvaluationContext.outputFuture, DemandNode.visibleAfter]
    change y ∈ body.variables ++ active
    exact List.mem_append_right _ hy
  | shrink profile context =>
    intro y hvisible hfuture
    have hactiveY : y ∈ context.expected.frame.active := (hactive y).2 hvisible
    rw [eachBodyOutputFuture] at hfuture
    simp only [List.mem_append] at hfuture
    rcases hfuture with hbody | houter
    · simp only [List.mem_filter, List.contains_iff_mem] at hbody
      exact List.mem_append_left _ hbody.2
    · exact List.mem_append_right _ houter

private theorem eachBody_retains_generated_alias {path : List Nat} {x : VarId}
    {idx : Option VarId} {sourceView : View} {byRef : Bool} {body : Block}
    {origin : OriginId} {penv : PEnv} {pc : PlanContext m plans}
    {context : NodeContext pc path
      (.statement (.forEach x idx sourceView byRef body origin)) .statement}
    (profile : m.profile = .shrink) (hAccessEq : pc.approvals.access = penv.access)
    {aliases : List RetainedAlias} {alias : RetainedAlias}
    (hgenerated : (DemandNode.statement (.forEach x idx sourceView byRef body origin)).retainedForChild
      penv.access path 1 = .ok aliases) (hmem : alias ∈ aliases) :
    alias ∈ (eachBodyContext (.shrink profile context)).retained := by
    let transition := context.child (by simp [DemandNode.primaryPhase]) 1 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
    have hgenerated' : (DemandNode.statement (.forEach x idx sourceView byRef body origin)).retainedForChild
        pc.approvals.access path 1 = .ok aliases := by
      simpa [hAccessEq] using hgenerated
    have hchild := DemandNode.childFrame_newAlias transition.childFrameEq hgenerated' hmem
    have hphase := DemandNode.phaseFrame_retains transition.phaseFrameEq hchild
    change alias ∈ transition.context.expected.frame.retained
    rw [transition.expectedFrameEq]
    exact hphase

private theorem shrinkAccessEq {path : List Nat} {node : DemandNode} {phase : DemandPhase}
    {tenv : TEnv} {penv : PEnv} {pc : PlanContext m plans}
    {context : NodeContext pc path node phase} (profile : m.profile = .shrink)
    (haccess : (EvaluationContext.shrink profile context).AccessMatches tenv penv) :
    pc.approvals.access = penv.access := by
  change pc.approvals.access.mod = tenv.mod ∧
    pc.approvals.access.impl.vars = tenv.vars ∧
    pc.approvals.access.mod = penv.mod ∧
    pc.approvals.access.impl = penv.impl ∧
    pc.approvals.access.ctx = penv.ctx at haccess
  rcases haccess with ⟨_, _, hmod, himpl, hctx⟩
  cases penv with
  | mk pmod pimp pctx scopes =>
    cases hmod
    cases himpl
    cases hctx
    rfl

private theorem aliasView_ok_singleton (access : AccessEnv) (path : List Nat) (view : View)
    {aliases : List RetainedAlias}
    (h : access.aliasView path view = .ok aliases) : ∃ alias, aliases = [alias] := by
  unfold AccessEnv.aliasView at h
  cases htype : access.viewElement? view with
  | none => simp [htype, reject] at h
  | some el =>
    rw [htype] at h
    cases hroots : access.viewRoots view with
    | error err =>
      rw [hroots] at h
      change Except.error err = .ok aliases at h
      cases h
    | ok roots =>
      simp only [hroots] at h
      refine ⟨⟨.slice .readOnly el, roots, .operand path⟩, ?_⟩
      cases h
      rfl

private theorem aliasPlace_owner_ok_singleton (access : AccessEnv) (path : List Nat) (place : Place)
    (elTy : Ty) (htype : access.placeType? place = some elTy)
    (howner : elTy.ownerElem?.isSome = true) {aliases : List RetainedAlias}
    (h : access.aliasPlace path place = .ok aliases) : ∃ alias, aliases = [alias] := by
  unfold AccessEnv.aliasPlace at h
  rw [htype] at h
  have htarget : ((Ty.ref .mutable elTy).interiorTarget?.isSome || elTy.ownerElem?.isSome) = true := by
    simp [howner]
  simp only [htarget] at h
  cases hroots : access.placeRoots place with
  | error err =>
    rw [hroots] at h
    change Except.error err = .ok aliases at h
    cases h
  | ok roots =>
    simp only [hroots] at h
    refine ⟨⟨.ref .mutable elTy, roots, .operand path⟩, ?_⟩
    exact Except.ok.inj h |>.symm

private def EachAliasQuery (access : AccessEnv) (path : List Nat) (sourceView : View)
    (alias : RetainedAlias) : Prop :=
  match sourceView with
  | .val _ => access.aliasView (path ++ [0]) sourceView = .ok [alias]
  | .of place =>
    match access.placeType? place with
    | none => access.aliasView (path ++ [0]) sourceView = .ok [alias]
    | some ty =>
      if ty.ownerElem?.isSome then access.aliasPlace (path ++ [0]) place = .ok [alias]
      else access.aliasView (path ++ [0]) sourceView = .ok [alias]

private theorem forEach_retained_query_exists {access : AccessEnv} {path : List Nat} {x : VarId}
    {idx : Option VarId} {sourceView : View} {byRef : Bool} {body : Block} {origin : OriginId}
    {aliases : List RetainedAlias}
    (hret : (DemandNode.statement (.forEach x idx sourceView byRef body origin)).retainedForChild
      access path 1 = .ok aliases) :
    ∃ alias, aliases = [alias] ∧ EachAliasQuery access path sourceView alias := by
  cases sourceView with
  | val e =>
    have hquery : access.aliasView (path ++ [0]) (.val e) = .ok aliases := by
      simpa [DemandNode.retainedForChild] using hret
    obtain ⟨alias, hsingle⟩ := aliasView_ok_singleton access (path ++ [0]) (.val e) hquery
    refine ⟨alias, hsingle, ?_⟩
    simpa [EachAliasQuery] using hquery.trans (congrArg Except.ok hsingle)
  | of place =>
    cases htype : access.placeType? place with
    | none =>
      have hquery : access.aliasView (path ++ [0]) (.of place) = .ok aliases := by
        simpa [DemandNode.retainedForChild, htype] using hret
      obtain ⟨alias, hsingle⟩ := aliasView_ok_singleton access (path ++ [0]) (.of place) hquery
      refine ⟨alias, hsingle, ?_⟩
      simpa [EachAliasQuery, htype] using hquery.trans (congrArg Except.ok hsingle)
    | some ty =>
      by_cases howner : ty.ownerElem?.isSome = true
      · have hquery : access.aliasPlace (path ++ [0]) place = .ok aliases := by
          simpa [DemandNode.retainedForChild, htype, howner] using hret
        obtain ⟨alias, hsingle⟩ :=
          aliasPlace_owner_ok_singleton access (path ++ [0]) place ty htype howner hquery
        refine ⟨alias, hsingle, ?_⟩
        simpa [EachAliasQuery, htype, howner] using hquery.trans (congrArg Except.ok hsingle)
      · have hownerFalse : ty.ownerElem?.isSome = false := by
          cases hsome : ty.ownerElem?.isSome with
          | false => rfl
          | true => exact False.elim (howner hsome)
        have hquery : access.aliasView (path ++ [0]) (.of place) = .ok aliases := by
          simpa [DemandNode.retainedForChild, htype, hownerFalse] using hret
        obtain ⟨alias, hsingle⟩ := aliasView_ok_singleton access (path ++ [0]) (.of place) hquery
        refine ⟨alias, hsingle, ?_⟩
        simpa [EachAliasQuery, htype, hownerFalse] using hquery.trans (congrArg Except.ok hsingle)

private theorem retainedForChild_ok_of_childFrame {node : DemandNode} {access : AccessEnv}
    {path : List Nat} {frame : DemandFrame} {index : Nat} {result : DemandFrame}
    (h : node.childFrame access path frame index = .ok result) :
    ∃ aliases, node.retainedForChild access path index = .ok aliases := by
  unfold DemandNode.childFrame at h
  let parent : DemandPoint := ⟨path, .expression, frame.active, frame.future, frame.retained⟩
  cases hchild : node.childExpectation? access parent index with
  | none => simp [parent, hchild, reject] at h
  | some expectation =>
    have hbind : (node.retainedForChild access path index >>= fun aliases =>
        pure ⟨expectation.active, expectation.future, aliases ++ frame.retained⟩) = .ok result := by
      simpa [parent, hchild] using h
    obtain ⟨aliases, hretained, _⟩ := (ex_bind_ok _ _ _).1 hbind
    exact ⟨aliases, hretained⟩

private theorem aliasView_sameProjection {access : AccessEnv} {path path' : List Nat} {view : View}
    {alias alias' : RetainedAlias}
    (h : access.aliasView path view = .ok [alias])
    (h' : access.aliasView path' view = .ok [alias']) :
    alias.ty = alias'.ty ∧ alias.roots = alias'.roots := by
  obtain ⟨el, roots, htype, hroots, hshape⟩ := AccessEnv.aliasView_singleton access path view alias h
  obtain ⟨el', roots', htype', hroots', hshape'⟩ :=
    AccessEnv.aliasView_singleton access path' view alias' h'
  have hel : el = el' := Option.some.inj (htype.symm.trans htype')
  have hrootsEq : roots = roots' := Except.ok.inj (hroots.symm.trans hroots')
  rw [hshape, hshape']
  simp [hel, hrootsEq]

private theorem aliasPlace_sameProjection {access : AccessEnv} {path path' : List Nat} {place : Place}
    {alias alias' : RetainedAlias}
    (h : access.aliasPlace path place = .ok [alias])
    (h' : access.aliasPlace path' place = .ok [alias']) :
    alias.ty = alias'.ty ∧ alias.roots = alias'.roots := by
  obtain ⟨ty, roots, htype, hroots, hshape⟩ := AccessEnv.aliasPlace_singleton access path place alias h
  obtain ⟨ty', roots', htype', hroots', hshape'⟩ :=
    AccessEnv.aliasPlace_singleton access path' place alias' h'
  have hty : ty = ty' := Option.some.inj (htype.symm.trans htype')
  have hrootsEq : roots = roots' := Except.ok.inj (hroots.symm.trans hroots')
  rw [hshape, hshape']
  simp [hty, hrootsEq]

private theorem AliasAt.retag {m : Module} {W : World} {env : Env} {s : Store}
    {alias alias' : RetainedAlias} {value : Val}
    (hty : alias'.ty = alias.ty) (hroots : alias'.roots = alias.roots)
    (h : AliasAt m W env s alias value) : AliasAt m W env s alias' value := by
  exact ⟨hty ▸ h.1, fun r hr => hroots ▸ h.2 r hr⟩

private theorem AliasAt.sliceTy {m : Module} {W : World} {env : Env} {s : Store}
    {alias : RetainedAlias} {vw : ViewVal} {el : Ty}
    (htype : alias.ty = .slice .readOnly el)
    (h : AliasAt m W env s alias (.slice vw.loc vw.start vw.len)) :
    SliceTy s vw.loc vw.start vw.len el := by
  have htyped := h.1
  rw [htype] at htyped
  obtain ⟨loc, start, len, heq, _, hslice⟩ := htyped
  injection heq with hloc hstart hlen
  cases hloc
  cases hstart
  cases hlen
  exact hslice

private theorem eachViewAfterBody {m : Module} {W : World} {penv : PEnv} {env : Env}
    {s s' : Store} {source : View} {vw : ViewVal} {el : Ty} {path : List Nat}
    {alias : RetainedAlias}
    (hEach : EachViewOk s vw el)
    (hAliases : ViewAliases m W penv env s source vw el)
    (hRetains : RetainsAlias m W env s s' alias)
    (hquery : EachAliasQuery penv.access path source alias) :
    EachViewOk s' vw el ∧ ViewAliases m W penv env s' source vw el := by
  cases hAliases with
  | fixed hresize hsource hrealized =>
    have hviewQuery : penv.access.aliasView (path ++ [0]) source = .ok [alias] := by
      rcases hsource with ⟨e, heq⟩ | ⟨place, count, heq, htype⟩
      · subst source
        simpa [EachAliasQuery] using hquery
      · subst source
        simpa [EachAliasQuery, htype, Ty.ownerElem?] using hquery
    obtain ⟨htype, hAliasAt⟩ := hrealized (path ++ [0]) alias hviewQuery
    have hAliasAtPost := hRetains.typed (.slice vw.loc vw.start vw.len) hAliasAt
    have hslice : SliceTy s' vw.loc vw.start vw.len el := by
      apply AliasAt.sliceTy htype
      exact hAliasAtPost
    refine ⟨⟨hEach.1, fun _ => hslice, ?_⟩, ?_⟩
    · intro htrue
      rw [hresize] at htrue
      cases htrue
    apply ViewAliases.fixed hresize hsource
    intro path' alias' hquery'
    obtain ⟨htype', _⟩ := hrealized path' alias' hquery'
    have hprojection := aliasView_sameProjection hviewQuery hquery'
    exact ⟨htype', AliasAt.retag hprojection.1.symm hprojection.2.symm hAliasAtPost⟩
  | limited hresize place capacity hsource htype hbound hrealized =>
    have hplaceQuery : penv.access.aliasPlace (path ++ [0]) place = .ok [alias] := by
      simpa [EachAliasQuery, hsource, htype, Ty.ownerElem?] using hquery
    obtain ⟨htypeAlias, hAliasAt⟩ := hrealized (path ++ [0]) alias hplaceQuery
    have hslice : SliceTy s' vw.loc vw.start vw.len el :=
      hRetains.physicalLimited .mutable el capacity vw.loc vw.start vw.len htypeAlias
        hAliasAt (hEach.2.1 hresize)
    have hAliasAtPost := hRetains.typed (.ref vw.loc) hAliasAt
    refine ⟨⟨hEach.1, fun _ => hslice, ?_⟩, ?_⟩
    · intro htrue
      rw [hresize] at htrue
      cases htrue
    apply ViewAliases.limited hresize place capacity hsource htype hbound
    intro path' alias' hquery'
    obtain ⟨htype', _⟩ := hrealized path' alias' hquery'
    have hprojection := aliasPlace_sameProjection hplaceQuery hquery'
    exact ⟨htype', AliasAt.retag hprojection.1.symm hprojection.2.symm hAliasAtPost⟩
  | owner hresize place owner hsource howner htype hbound hrealized =>
    have hplaceQuery : penv.access.aliasPlace (path ++ [0]) place = .ok [alias] := by
      rcases howner with howner | howner
      · subst owner
        simpa [EachAliasQuery, hsource, htype, Ty.ownerElem?] using hquery
      · subst owner
        simpa [EachAliasQuery, hsource, htype, Ty.ownerElem?] using hquery
    have hownerAlias : AliasAt m W env s' alias (.ref vw.loc) :=
      hRetains.typed (.ref vw.loc) (hrealized (path ++ [0]) alias hplaceQuery).2
    have hownerLoc : LocTy s' vw.loc owner := hownerAlias.ownerLocation
      (hrealized (path ++ [0]) alias hplaceQuery).1 howner hbound
    have hEachPost : EachViewOk s' vw el := by
      refine ⟨hEach.1, ?_, ?_⟩
      · intro hfalse
        rw [hresize] at hfalse
        cases hfalse
      · intro htrue
        obtain ⟨hstart, _⟩ := hEach.2.2 htrue
        refine ⟨hstart, ?_⟩
        rcases howner with h | h
        · exact Or.inl (h ▸ hownerLoc)
        · exact Or.inr (h ▸ hownerLoc)
    refine ⟨hEachPost, ?_⟩
    apply ViewAliases.owner hresize place owner hsource howner htype hbound
    intro path' alias' hquery'
    obtain ⟨htype', _⟩ := hrealized path' alias' hquery'
    have hprojection := aliasPlace_sameProjection hplaceQuery hquery'
    exact ⟨htype', AliasAt.retag hprojection.1.symm hprojection.2.symm hownerAlias⟩

private theorem eachViewOk_mono {s s' : Store} {vw : ViewVal} {el : Ty}
    (hle : StoreLe s s') (h : EachViewOk s vw el) : EachViewOk s' vw el := by
  refine ⟨h.1, fun hfixed => (h.2.1 hfixed).mono hle, ?_⟩
  intro hresizable
  obtain ⟨hstart, howner⟩ := h.2.2 hresizable
  refine ⟨hstart, howner.elim (fun h => Or.inl (LocTy.mono hle h))
    (fun h => Or.inr (LocTy.mono hle h))⟩

private theorem retOk_tenv_congr {m : Module} {W : World} {tenv tenv' : TEnv}
    {penv penv' : PEnv} {s : St} {v : Val}
    (h : RetOk m W tenv' penv' s v) (htenv : tenv'.impl = tenv.impl)
    (hpenv : penv'.ctx = penv.ctx) : RetOk m W tenv penv s v := by
  obtain ⟨impl, himpl, hresult, htargets⟩ := h
  exact ⟨impl, htenv ▸ himpl, hresult, hpenv ▸ htargets⟩

set_option maxHeartbeats 800000 in
theorem step_while (ih : Specs m prof plans n) : WhileSpec m prof plans (n + 1) := by
  intro path c body origin ec observation W tenv penv env s tn tn1 tn2 bty rst rst1 rst2 rhoc rb rng
    hactive haccess hprotected hobserved hclassified hp hF htc htb hrc hrb hE
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
  have hmayCondition : ∀ r, conditionEc.mayShrink W.ownerP observation r ↔ ec.mayShrink W.ownerP observation r := by
    intro r
    exact ec.child_mayShrink_iff (by simp [DemandNode.primaryPhase]) 0 (.expression c) .expression
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) W.ownerP observation r
  have hmayBody : ∀ r, bodyEc.mayShrink W.ownerP observation r ↔ ec.mayShrink W.ownerP observation r := by
    intro r
    exact ec.child_mayShrink_iff (by simp [DemandNode.primaryPhase]) 1 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) W.ownerP observation r
  have hprotectedCondition : ShrinkProtected W.D W.A (conditionEc.mayShrink W.ownerP observation) :=
    ShrinkProtected.mono hprotected (fun _ _ h => h) (fun _ _ h => h)
      (fun r h => (hmayCondition r).1 h)
  have hprotectedBody : ShrinkProtected W.D W.A (bodyEc.mayShrink W.ownerP observation) :=
    ShrinkProtected.mono hprotected (fun _ _ h => h) (fun _ _ h => h)
      (fun r h => (hmayBody r).1 h)
  have hobservedCondition : ObservedSafe m W (conditionEc.mayShrink W.ownerP observation) observation s.store :=
    hobserved.weakenShrinking (fun r h => (hmayCondition r).1 h)
  have hobservedBody : ObservedSafe m W (bodyEc.mayShrink W.ownerP observation) observation s.store :=
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
  have hMutationRoots : ∀ r,
      r ∈ effectMutationRoots m penv.impl rst1.eff →
        r ∈ effectMutationRoots m penv.impl rst2.eff :=
    effectMutationRoots.mono m penv.impl (rpBlockValue_mono hrb).2
      (rpBlockValue_rebinds_mono hrb)
  have body_part : ∀ (s1 : St), Frame m W loopT penv env s1 bodyEc.inputFuture →
      Footprint (insts env) (Dset W) s s1 →
      PreservesRootTypes m W.G observation.roots s.store s1.store →
      PreservesValues m W.G observation.values s.store s1.store →
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s1.store →
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s1.store) →
      RetainsAliases m W env s.store s1.store ec.retained →
      PilotStoreLe m s s1 →
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s1 →
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst2.eff) s s1 →
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
        ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
        RetainsAliases m W env s.store s'.store ec.retained ∧
        PilotStoreLe m s s' ∧ LoopFlow m W tenv penv s' fl ∧
        (∀ v, fl = .normal v → c = .bool true → body.hasBreak = true) ∧
        (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store) ∧
        PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
          ec.forbiddenOwners s s' ∧
        MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst2.eff) s s') := by
    intro s1 hF1 hFoot1 hRoots1 hValues1 hSafe1 hClass1 hRetained1 hPilot1 hForbidden1 hMutation1
    have hSafeBody1 : ObservedSafe m W (bodyEc.mayShrink W.ownerP observation) observation s1.store :=
      hSafe1.weakenShrinking (fun r h => (hmayBody r).1 h)
    refine Sat.bind (block_of_checks ih.block hp body bodyEc observation [] []
      hBodyActiveAfterDeclare haccessBody hprotectedBody hSafeBody1 hClass1 hF1 htb hrb hE rfl rfl
      (fun _ _ _ _ h => by simp at h)) ?_
    rintro fl s2 ⟨hF2, hFoot2, hRoots2, hValues2, hSafe2, hRetained2, hPilot2,
      hFlow, hClass2, hForbidden2, hMutation2⟩
    have hSafe2Parent : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s2.store :=
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
    have hForbidden2Parent : PreservesForbiddenOwnerRoots (m := m) (G := W.G)
        (env := env) (P := W.P) ec.forbiddenOwners s1 s2 :=
      hForbidden2.subset (fun owner howner =>
        ec.child_forbidden_subset (by simp [DemandNode.primaryPhase]) 1 (.block body) .block
          (by simp [DemandNode.child?, DemandNode.children])
          (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) owner howner)
    have hForbidden2Start := hForbidden1.trans hForbidden2Parent
    have hMutation2Start := hMutation1.trans hMutation2
    cases fl with
    | normal v =>
      have hAgain := ih.while_ path c body origin ec observation W tenv penv env s2 tn tn1 tn2 bty
        rst rst1 rst2 rhoc rb rng hactive haccess hprotected hSafe2Parent hClass2 hp hF2LoopInput
        htc htb hrc hrb hE
      exact hAgain.mono (fun fl3 s3 ⟨hF3, hFoot3, hRoots3, hValues3, hSafe3, hRetained3,
          hPilot3, hFlow3, hBreak3, hClass3, hForbidden3, hMutation3⟩ =>
        ⟨hF3, hFoot2Start.trans hFoot3, hRoots2Start.trans hRoots3,
          hValues2Start.trans hValues3, hSafe3, hRetained2Start.trans hRetained3,
          (fun hpilot => (hPilot2Start hpilot).trans (hPilot3 hpilot)), hFlow3, hBreak3,
          hClass3, hForbidden2Start.trans hForbidden3, hMutation2Start.trans hMutation3⟩)
    | cont =>
      have hAgain := ih.while_ path c body origin ec observation W tenv penv env s2 tn tn1 tn2 bty
        rst rst1 rst2 rhoc rb rng hactive haccess hprotected hSafe2Parent hClass2 hp hF2LoopInput
        htc htb hrc hrb hE
      exact hAgain.mono (fun fl3 s3 ⟨hF3, hFoot3, hRoots3, hValues3, hSafe3, hRetained3,
          hPilot3, hFlow3, hBreak3, hClass3, hForbidden3, hMutation3⟩ =>
        ⟨hF3, hFoot2Start.trans hFoot3, hRoots2Start.trans hRoots3,
          hValues2Start.trans hValues3, hSafe3, hRetained2Start.trans hRetained3,
          (fun hpilot => (hPilot2Start hpilot).trans (hPilot3 hpilot)), hFlow3, hBreak3,
          hClass3, hForbidden2Start.trans hForbidden3, hMutation2Start.trans hMutation3⟩)
    | brk =>
      simp only [sat_pure]
      exact ⟨hF2LoopOutput, hFoot2Start, hRoots2Start, hValues2Start, hSafe2Parent,
        hRetained2Start, hPilot2Start, trivial, fun _ _ _ => hFlow.2, hClass2,
        hForbidden2Start, hMutation2Start⟩
    | ret v =>
      simp only [sat_pure]
      exact ⟨hF2LoopOutput, hFoot2Start, hRoots2Start, hValues2Start, hSafe2Parent,
        hRetained2Start, hPilot2Start, ⟨hFlow.1, retOk_tenv_congr hFlow.2 rfl rfl⟩,
        (fun v' h => by cases h), hClass2, hForbidden2Start, hMutation2Start⟩
  by_cases hc : c = .bool true
  · subst hc
    rw [execWhile, evalExpr_bool]
    by_cases hn : n = 0
    · rw [if_pos hn]; exact trivial
    · rw [if_neg hn]
      exact body_part s hFBody (Footprint.refl (insts env) (Dset W) s)
        (PreservesRootTypes.refl s.store) (PreservesValues.refl s.store) hobserved
        hclassified RetainsAliases.refl (by intro _; exact StoreLe.refl _)
        (PreservesForbiddenOwnerRoots.refl s)
        (MutationFootprint.refl env W.P W.base (effectMutationRoots m penv.impl rst2.eff) s)
  · simp only [execWhile]
    refine Sat.bind (ih.expr (path ++ [0]) c conditionEc observation W tenv penv env s tn tn1 .bool
      rst rst1 rhoc hactiveCondition haccessCondition hprotectedCondition hobservedCondition hclassified hp hFCondition
      htc hrc
      ((rpBlockValue_mono hrb).2.trans hE)) ?_
    rintro vc s1 ⟨hF1, hFoot1, hRoots1, hValues1, hSafe1, hRetained1, hPilot1,
      hv, _, hClass1, _, hForbidden1, hMutation1⟩
    obtain ⟨x, rfl⟩ := hasTy_bool hv
    have hSafe1Parent : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s1.store :=
      hSafe1.weakenShrinking (fun r h => (hmayCondition r).2 h)
    have hRetained1Parent : RetainsAliases m W env s.store s1.store ec.retained :=
      hRetained1.subset (fun alias hmem =>
        ec.child_retained_subset (by simp [DemandNode.primaryPhase]) 0 (.expression c) .expression
          (by simp [DemandNode.child?, DemandNode.children])
          (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) hmem)
    have hForbidden1Parent : PreservesForbiddenOwnerRoots (m := m) (G := W.G)
        (env := env) (P := W.P) ec.forbiddenOwners s s1 :=
      hForbidden1.subset (fun owner howner =>
        ec.child_forbidden_subset (by simp [DemandNode.primaryPhase]) 0 (.expression c) .expression
          (by simp [DemandNode.child?, DemandNode.children])
          (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) owner howner)
    have hMutation1Final : MutationFootprint env W.P W.base
        (effectMutationRoots m penv.impl rst2.eff) s s1 :=
      MutationFootprint.weaken hMutation1 hMutationRoots
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
        hPilot1, trivial, fun _ _ h => absurd h hc, hClass1,
        hForbidden1Parent, hMutation1Final⟩
    · simp only [if_true]
      exact body_part s1 hF1Body hFoot1 hRoots1 hValues1 hSafe1Parent hClass1
        hRetained1Parent hPilot1 hForbidden1Parent hMutation1Final

set_option maxHeartbeats 800000 in
theorem step_range (ih : Specs m prof plans n) : RangeSpec m prof plans (n + 1) := by
  intro path x lower upper body origin ec observation W tenv penv env s t i hi tn1 tn2 bty rst1 rst2 rb rng
    hactive haccess hprotected hobserved hclassified hp hF hx hlt htb hrb hE hk0
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
  have hmayBody : ∀ r, bodyEc.mayShrink W.ownerP observation r ↔ ec.mayShrink W.ownerP observation r := by
    intro r
    exact ec.child_mayShrink_iff (by simp [DemandNode.primaryPhase]) 2 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) W.ownerP observation r
  have hprotectedBody : ShrinkProtected W.D W.A (bodyEc.mayShrink W.ownerP observation) :=
    ShrinkProtected.mono hprotected (fun _ _ h => h) (fun _ _ h => h)
      (fun r h => (hmayBody r).1 h)
  have hobservedBody : ObservedSafe m W (bodyEc.mayShrink W.ownerP observation) observation s.store :=
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
      hBodyActiveAfterDeclare haccessBody hprotectedBody hobservedBody hclassified hFBody htb hrb hE
      rfl (by simp) ?_ (Nat.le_of_lt hlt) hk0) ?_
    · intro x' v hm
      simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      refine ⟨Nat.le_refl _, hlt, lv, hlv, hsc, by rw [hty]; rfl, ?_, fun r hr => hr.elim⟩
      rw [hty]
      exact hasTy_of_flat (T := .int t) (show FlatTy (.int t) (.int t i) from rfl) (Or.inl rfl)
    · rintro fl s2 ⟨hF2, hFoot2, hRoots2, hValues2, hSafe2, hRetained2,
          hPilot2, hFlow, hClass2, hForbidden2, hMutation2⟩
      have hSafe2Parent : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s2.store :=
        hSafe2.weakenShrinking (fun r h => (hmayBody r).2 h)
      have hRetained2Parent : RetainsAliases m W env s.store s2.store ec.retained :=
        hRetained2.subset (fun alias hmem =>
          ec.child_retained_subset (by simp [DemandNode.primaryPhase]) 2 (.block body) .block
            (by simp [DemandNode.child?, DemandNode.children])
            (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) hmem)
      have hForbidden2Parent : PreservesForbiddenOwnerRoots (m := m) (G := W.G)
          (env := env) (P := W.P) ec.forbiddenOwners s s2 :=
        hForbidden2.subset (fun owner howner =>
          ec.child_forbidden_subset (by simp [DemandNode.primaryPhase]) 2 (.block body) .block
            (by simp [DemandNode.child?, DemandNode.children])
            (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) owner howner)
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
          (i + 1) hi tn1 tn2 bty rst1 rst2 rb rng hactive haccess hprotected hSafe2Parent hClass2 hp
          hF2LoopInput ⟨lv, hlv, hsc, hty⟩ hlt htb hrb hE hk0
        exact hAgain.mono (fun fl3 s3
          ⟨hF3, hFoot3, hRoots3, hValues3, hSafe3, hRetained3, hPilot3, hFlow3,
            hClass3, hForbidden3, hMutation3⟩ =>
            ⟨hF3, hFoot2.trans hFoot3, hRoots2.trans hRoots3, hValues2.trans hValues3,
              hSafe3, hRetained2Parent.trans hRetained3,
              (fun hpilot => (hPilot2 hpilot).trans (hPilot3 hpilot)), hFlow3, hClass3,
              hForbidden2Parent.trans hForbidden3, hMutation2.trans hMutation3⟩)
      | cont =>
        have hAgain := ih.range path x lower upper body origin ec observation W tenv penv env s2 t
          (i + 1) hi tn1 tn2 bty rst1 rst2 rb rng hactive haccess hprotected hSafe2Parent hClass2 hp
          hF2LoopInput ⟨lv, hlv, hsc, hty⟩ hlt htb hrb hE hk0
        exact hAgain.mono (fun fl3 s3
          ⟨hF3, hFoot3, hRoots3, hValues3, hSafe3, hRetained3, hPilot3, hFlow3,
            hClass3, hForbidden3, hMutation3⟩ =>
            ⟨hF3, hFoot2.trans hFoot3, hRoots2.trans hRoots3, hValues2.trans hValues3,
              hSafe3, hRetained2Parent.trans hRetained3,
              (fun hpilot => (hPilot2 hpilot).trans (hPilot3 hpilot)), hFlow3, hClass3,
              hForbidden2Parent.trans hForbidden3, hMutation2.trans hMutation3⟩)
      | brk =>
        simp only [sat_pure]
        exact ⟨hF2LoopOutput, hFoot2, hRoots2, hValues2, hSafe2Parent, hRetained2Parent,
          hPilot2, trivial, hClass2, hForbidden2Parent, hMutation2⟩
      | ret v =>
        simp only [sat_pure]
        exact ⟨hF2LoopOutput, hFoot2, hRoots2, hValues2, hSafe2Parent, hRetained2Parent,
          hPilot2, ⟨hFlow.1, retOk_tenv_congr hFlow.2 rfl rfl⟩,
          hClass2, hForbidden2Parent, hMutation2⟩
  · simp only [h, if_false, sat_pure]
    exact ⟨hF.narrowFuture (fun _ h => List.mem_append_right _ h),
      Footprint.refl (insts env) (Dset W) s, PreservesRootTypes.refl s.store,
      PreservesValues.refl s.store, hobserved, RetainsAliases.refl,
      (fun _ => StoreLe.refl _), trivial, hclassified,
      PreservesForbiddenOwnerRoots.refl s,
      MutationFootprint.refl env W.P W.base (effectMutationRoots m penv.impl rst2.eff) s⟩

set_option maxHeartbeats 1600000 in
theorem step_each (ih : Specs m prof plans n) : EachSpec m prof plans (n + 1) := by
  intro path x idx sourceView byRef body origin ec observation W tenv penv env s vw i el rho
    tn1 tn2 bty rst1 rst2 rb rng hactive haccess hprotected hobserved hclassified hp hF hvw hViewAliases hg
    hx hj hlt htb hrb hE hk0
  let bodyEc := eachBodyContext ec
  let loopT := { tenv with loops := tenv.loops + 1 }
  let loopVars := x :: idx.toList
  have hactiveLoop : ec.ActiveMatches loopT := by
    simpa [EvaluationContext.ActiveMatches, NodeContext.ActiveMatches, loopT] using hactive
  have haccessLoop : ec.AccessMatches loopT penv := by
    simpa [EvaluationContext.AccessMatches, NodeContext.AccessMatches, loopT] using haccess
  have haccessBody : bodyEc.AccessMatches loopT penv :=
    (ec.child_accessMatches_iff (by simp [DemandNode.primaryPhase]) 1 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) loopT penv).2 haccessLoop
  have hmayBody : ∀ r, bodyEc.mayShrink W.ownerP observation r ↔ ec.mayShrink W.ownerP observation r := by
    intro r
    exact ec.child_mayShrink_iff (by simp [DemandNode.primaryPhase]) 1 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) W.ownerP observation r
  have hprotectedBody : ShrinkProtected W.D W.A (bodyEc.mayShrink W.ownerP observation) :=
    ShrinkProtected.mono hprotected (fun _ _ h => h) (fun _ _ h => h)
      (fun r h => (hmayBody r).1 h)
  have hFLoop : Frame m W loopT penv env s (body.variables ++ ec.outputFuture) :=
    hF.tenv_congr rfl rfl rfl (fun _ h => h)
  have hFBody : Frame m W loopT penv env s bodyEc.inputFuture := by
    have hInputFuture : bodyEc.inputFuture = body.variables ++ bodyEc.outputFuture := by
      cases ec <;> rfl
    rw [hInputFuture]
    exact hFLoop.changeFuture (fun y hvisible hfuture => by
      rcases List.mem_append.mp hfuture with hbody | houtput
      · exact List.mem_append_left _ hbody
      · exact eachBodyOutput_subsetInput ec hactive y (by simpa [loopT] using hvisible) houtput)
  have hBodyActiveAfterDeclare : ∀ env1 tnEnd,
      declarePre { {loopT with visible := loopVars ++ loopT.visible} with scopes := body.scope :: loopT.scopes }
          body.scope [] tn1 = .ok (env1, tnEnd) → bodyEc.ActiveMatches env1 := by
    intro env1 tnEnd hdeclare
    obtain ⟨_, hvis, _, _⟩ := declarePre_ok _ _ _ _ _ _ hdeclare
    have hvisible : ∀ y, y ∈ env1.visible ↔ y ∈ loopVars ++ tenv.visible := by
      intro y
      simpa [loopT, loopVars] using hvis y
    exact ec.child_activeMatches (by simp [DemandNode.primaryPhase]) 1 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) tenv env1 hactive
      (by
        intro y
        change y ∈ env1.visible ↔ y ∈ (x :: idx.toList).foldl
          (fun active binder => if active.contains binder then active else binder :: active)
          tenv.visible
        exact (hvisible y).trans (foldVisibleIff (binders := x :: idx.toList)
          (active := tenv.visible) (y := y)).symm)
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
    · rw [if_pos h]
      have hel : LocTy s'.store ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩ el := sliceTy_elem hsl h
      have hFl : Frame m W loopT penv env s' bodyEc.inputFuture := hFBody
      obtain ⟨lv, hlv, hsc, hst, hxty⟩ := hx
      have hnotOwnerTy : ¬ OwnerRefTy lv.ty := by
        have hflat : el.flat = true := hvw.1
        cases byRef with
        | false =>
          have hty : lv.ty = el := by simpa using hxty
          rw [hty]
          intro howner
          rcases howner with ⟨mu, target, htarget | htarget⟩ <;>
            cases htarget <;> simp [Ty.flat] at hflat
        | true =>
          rcases hxty with ⟨⟨mu, hty⟩, _⟩
          rw [hty]
          intro howner
          rcases howner with ⟨mu', target, htarget | htarget⟩ <;>
            cases htarget <;> simp [Ty.flat] at hflat
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
              Gam env W.P ann r ∧ (OwnerRefTy lv.ty → Gam env W.ownerP ann r)) →
          Sat (execBlock n ⟨prof, m⟩ env ((x, ev) :: pre') body >>= fun fl =>
            match fl with
            | .normal _ => execEach n ⟨prof, m⟩ env x idx byRef body vw (i + 1)
            | .cont => execEach n ⟨prof, m⟩ env x idx byRef body vw (i + 1)
            | .brk => pure (.normal .unit)
            | .ret v => pure (.ret v)) s' (fun fl s2 =>
            Frame m W tenv penv env s2 ec.outputFuture ∧
              Footprint (insts env) (Dset W) s' s2 ∧
              PreservesRootTypes m W.G observation.roots s'.store s2.store ∧
              PreservesValues m W.G observation.values s'.store s2.store ∧
              ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s2.store ∧
              RetainsAliases m W env s'.store s2.store ec.retained ∧
              PilotStoreLe m s' s2 ∧ LoopFlow m W tenv penv s2 fl ∧
              (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s2.store) ∧
              PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
                ec.forbiddenOwners s' s2 ∧
              MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst2.eff) s' s2) := by
        intro ev pre' hpre' hev
        subst hpre'
        have hSafeBody : ObservedSafe m W (bodyEc.mayShrink W.ownerP observation) observation s'.store :=
          hobserved.weakenShrinking (fun r h => (hmayBody r).1 h)
        refine Sat.bind (block_of_reserved ih.block hp body bodyEc observation
          ((x, ev) :: idxVal i idx) loopVars x hBodyActiveAfterDeclare haccessBody hprotectedBody
          hSafeBody hclassified hFl htb hrb hE (by cases idx <;> rfl) hnd ?_
          (Nat.le_of_lt hxlt) hk0) ?_
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
        · rintro fl s2 ⟨hF2, hFoot2, hRoots2, hValues2, hSafe2, hRetained2,
            hPilot2, hfl, hClass2, hForbidden2, hMutation2⟩
          have hSafe2Parent : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s2.store :=
            hSafe2.weakenShrinking (fun r h => (hmayBody r).2 h)
          have hRetained2Parent : RetainsAliases m W env s'.store s2.store ec.retained :=
            hRetained2.subset (fun alias hmem =>
              ec.child_retained_subset (by simp [DemandNode.primaryPhase]) 1 (.block body) .block
                (by simp [DemandNode.child?, DemandNode.children])
                (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) hmem)
          have hForbidden2Parent : PreservesForbiddenOwnerRoots (m := m) (G := W.G)
              (env := env) (P := W.P) ec.forbiddenOwners s' s2 :=
            hForbidden2.subset (fun owner howner =>
              ec.child_forbidden_subset (by simp [DemandNode.primaryPhase]) 1 (.block body) .block
                (by simp [DemandNode.child?, DemandNode.children])
                (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) owner howner)
          have hF2LoopInput : Frame m W tenv penv env s2 (body.variables ++ ec.outputFuture) := by
            have hF2Loop : Frame m W loopT penv env s2 (body.variables ++ ec.outputFuture) :=
              hF2.changeFuture (fun y hvisible hfuture =>
                eachBodyOutput_coversInput ec hactive y (by simpa [loopT] using hvisible) hfuture)
            exact hF2Loop.tenv_congr rfl rfl rfl (fun _ h => h)
          have hF2LoopOutput : Frame m W tenv penv env s2 ec.outputFuture := by
            have hF2Loop : Frame m W loopT penv env s2 ec.outputFuture :=
              hF2.changeFuture (fun y hvisible hfuture =>
                eachBodyOutput_coversOutput ec hactive y (by simpa [loopT] using hvisible) hfuture)
            exact hF2Loop.tenv_congr rfl rfl rfl (fun _ h => h)
          have hView2 : EachViewOk s2.store vw el ∧
              ViewAliases m W penv env s2.store sourceView vw el := by
            cases ec with
            | pilot profile active =>
              have hle : StoreLe s'.store s2.store := hPilot2 profile
              exact ⟨eachViewOk_mono hle hvw, ViewAliases.mono hle hViewAliases⟩
            | shrink profile context =>
              let transition := context.child (by simp [DemandNode.primaryPhase]) 1 (.block body) .block
                (by simp [DemandNode.child?, DemandNode.children])
                (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
              obtain ⟨aliases, hgenerated⟩ :=
                retainedForChild_ok_of_childFrame transition.childFrameEq
              have hAccessEq := shrinkAccessEq profile haccess
              have hgeneratedPenv :
                  (DemandNode.statement (.forEach x idx sourceView byRef body origin)).retainedForChild
                    penv.access path 1 = .ok aliases := by
                simpa [hAccessEq] using hgenerated
              obtain ⟨alias, hsingleton, hquery⟩ := forEach_retained_query_exists hgeneratedPenv
              have hmem : alias ∈ aliases := by rw [hsingleton]; simp
              have hbodyAlias : alias ∈ bodyEc.retained := by
                exact eachBody_retains_generated_alias profile hAccessEq hgeneratedPenv hmem
              have hRetainsAlias : RetainsAlias m W env s'.store s2.store alias :=
                hRetained2 alias hbodyAlias
              exact eachViewAfterBody hvw hViewAliases hRetainsAlias hquery
          have hAgain := (ih.each path x idx sourceView byRef body origin ec observation W tenv penv env s2 vw (i + 1) el rho
            tn1 tn2 bty rst1 rst2 rb rng hactive haccess hprotected hSafe2Parent hClass2 hp
            hF2LoopInput hView2.1 hView2.2 hg ⟨lv, hlv, hsc, hst, hxty⟩ hj hlt htb hrb hE hk0).mono
            (Q := fun fl s3 =>
              Frame m W tenv penv env s3 ec.outputFuture ∧
              Footprint (insts env) (Dset W) s' s3 ∧
              PreservesRootTypes m W.G observation.roots s'.store s3.store ∧
              PreservesValues m W.G observation.values s'.store s3.store ∧
              ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s3.store ∧
              RetainsAliases m W env s'.store s3.store ec.retained ∧
              PilotStoreLe m s' s3 ∧ LoopFlow m W tenv penv s3 fl ∧
              (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s3.store) ∧
              PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
                ec.forbiddenOwners s' s3 ∧
              MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst2.eff) s' s3)
            (fun fl3 s3 ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ =>
              ⟨g1, hFoot2.trans g2, hRoots2.trans g3, hValues2.trans g4, g5,
                hRetained2Parent.trans g6,
                (fun hpilot => (hPilot2 hpilot).trans (g7 hpilot)), g8, g9,
                hForbidden2Parent.trans g10, hMutation2.trans g11⟩)
          cases fl with
          | normal v => exact hAgain
          | cont => exact hAgain
          | brk =>
            simp only [sat_pure]
            exact ⟨hF2LoopOutput, hFoot2, hRoots2, hValues2, hSafe2Parent,
              hRetained2Parent, hPilot2, trivial, hClass2, hForbidden2Parent, hMutation2⟩
          | ret v =>
            simp only [sat_pure]
            exact ⟨hF2LoopOutput, hFoot2, hRoots2, hValues2, hSafe2Parent,
              hRetained2Parent, hPilot2,
              ⟨hfl.1, retOk_tenv_congr hfl.2 rfl rfl⟩,
              hClass2, hForbidden2Parent, hMutation2⟩
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
          exact ⟨ann, ha, hg.subset hsub, fun howner => False.elim (hnotOwnerTy howner)⟩
      | false =>
        simp only [Bool.false_eq_true, if_false]
        have hty : lv.ty = el := by simpa using hxty
        refine sat_readLoc_bind hel (fun ev _ hT => ?_)
        refine rest _ _ (by cases idx <;> rfl) ⟨?_, flat_no_targets hT⟩
        rw [hty]
        exact hasTy_of_flat hT (Or.inl hvw.1)
    · rw [if_neg h]
      simp only [sat_pure]
      exact ⟨hF.narrowFuture (fun _ h => List.mem_append_right _ h),
        Footprint.refl _ _ _, PreservesRootTypes.refl _, PreservesValues.refl _,
        hobserved, RetainsAliases.refl, fun _ => StoreLe.refl _, trivial, hclassified,
        PreservesForbiddenOwnerRoots.refl s',
        MutationFootprint.refl env W.P W.base (effectMutationRoots m penv.impl rst2.eff) s'⟩

end Goose.Core.Sound
