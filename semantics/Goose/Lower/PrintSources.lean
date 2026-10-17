import Goose.Lower.SourceContexts

namespace Goose.Lower

open Goose.Core Goose.Proofs.Memory
open Goose.Core.Sound

inductive PrintSourceCursor {cfg : Cfg} (env : Env) (fuel : Nat) (results : List Ty) :
    List PrintArg → St → Prop
  | nil {state : St} : PrintSourceCursor (cfg := cfg) env fuel results [] state
  | text {text : String} {args : List PrintArg} {state : St}
      (tail : PrintSourceCursor (cfg := cfg) env fuel results args state) :
      PrintSourceCursor (cfg := cfg) env fuel results (.text text :: args) state
  | expr {expr : Expr} {args : List PrintArg} {state : St}
      (source : ExprSource cfg env expr state)
      (printable : (∃ ty, source.ty = .int ty) ∨ source.ty = .bool)
      (metadata : SourceResults source.typingEnv source.rootsEnv results)
      (resume : ∀ {part final},
        execPrintArg (fuel + 1) cfg env (.expr expr) state = .ok part final →
        PrintSourceCursor (cfg := cfg) env fuel results args final) :
      PrintSourceCursor (cfg := cfg) env fuel results (.expr expr :: args) state

private def printSuffixFuture {cfg : Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {args : List PrintArg} {origin : OriginId}
    (context : EvaluationContext cfg plans path (.statement (.print args origin)) .statement)
    (rest : List PrintArg) : List VarId := rest.flatMap PrintArg.variables ++ context.outputFuture

private theorem printShrinkExprOutputFuture {cfg : Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {all : List PrintArg} {origin : OriginId} {pc : PlanContext cfg plans}
    (profile : cfg.profile = .shrink)
    (context : NodeContext pc path (.statement (.print all origin)) .statement)
    (offset : Nat) (expr : Expr) (rest : List PrintArg)
    (harg : all[offset]? = some (.expr expr)) (hrest : rest = all.drop (offset + 1)) :
    ((EvaluationContext.shrink profile context).child rfl offset (.expression expr) .expression
      (by simp [DemandNode.child?, DemandNode.children, harg])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture =
        printSuffixFuture (.shrink profile context) rest := by
  have hchild : (DemandNode.statement (.print all origin)).child? offset =
      some (.expression expr) := by
    simp [DemandNode.child?, DemandNode.children, harg]
  have hphase : DemandNodeHasPhase (.expression expr) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hoffset : offset < all.length := (List.getElem?_eq_some_iff.mp harg).1
  let transition := context.child rfl offset (.expression expr) .expression hchild hphase
  let parent : DemandPoint :=
    ⟨path, .expression, context.expected.frame.active, context.expected.frame.future,
      context.expected.frame.retained⟩
  have hexpectation :
      (DemandNode.statement (.print all origin)).childExpectation?
          pc.approvals.access parent offset =
        some ⟨(DemandNode.statement (.print all origin)).visibleForChild
            context.expected.frame.active offset,
          rest.flatMap PrintArg.variables ++ context.expected.frame.future⟩ := by
    simp [parent, DemandNode.childExpectation?, DemandNode.childFuture, hchild, hrest, hoffset]
  have hfuture : transition.childFrame.future =
      rest.flatMap PrintArg.variables ++ context.expected.frame.future := by
    exact DemandNode.childFrame_future transition.childFrameEq hexpectation
  change transition.context.expected.frame.future =
    rest.flatMap PrintArg.variables ++ context.expected.frame.future
  rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
    hfuture]
  simp [DemandNode.phaseFuture]

private theorem printSuffixFrame {cfg : Cfg} {env : Env} {args : List PrintArg} {origin : OriginId}
    {state : St} (source : StmtSource cfg env (.print args origin) state) :
    Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
      (printSuffixFuture source.context args) := by
  cases hcontext : source.context with
  | pilot profile active =>
      have frame := source.frame
      rw [hcontext] at frame
      simpa [printSuffixFuture, EvaluationContext.inputFuture, EvaluationContext.outputFuture,
        DemandNode.variables, Stmt.variables, PrintArg.variables, DemandNode.visibleAfter] using frame
  | shrink profile context =>
      have frame := source.frame
      rw [hcontext] at frame
      simpa [printSuffixFuture, EvaluationContext.inputFuture, EvaluationContext.outputFuture,
        NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables, Stmt.variables,
        PrintArg.variables] using frame

private theorem render_success_state {value : Val} {part : String} {before after : St}
    (done : render value before = .ok part after) : after = before := by
  cases value with
  | int ty n => simp [render] at done; cases done; rfl
  | bool value => cases value <;> simp [render] at done <;> cases done <;> rfl
  | unit => simp [render] at done; cases done
  | fixed elems => simp [render] at done; cases done
  | record id fields => simp [render] at done; cases done
  | resizable elem elems => simp [render] at done; cases done
  | limited elem capacity slots len => simp [render] at done; cases done
  | ref location => simp [render] at done; cases done
  | slice location start len => simp [render] at done; cases done

private theorem execPrintExpr_success {cfg : Cfg} {env : Env} {expr : Expr}
    {state final : St} {part : String} {fuel : Nat}
    (done : execPrintArg (fuel + 1) cfg env (.expr expr) state = .ok part final) :
    ∃ value after, evalExpr fuel cfg env expr state = .ok value after ∧
      render value after = .ok part after ∧ final = after := by
  simp only [execPrintArg] at done
  change M.bind' (evalExpr fuel cfg env expr) render state = .ok part final at done
  cases heval : evalExpr fuel cfg env expr state with
  | stop error stopped => simp [M.bind', heval] at done
  | ok value after =>
      simp only [M.bind', heval] at done
      have hstate := render_success_state done
      subst final
      exact ⟨value, after, rfl, done, rfl⟩

private theorem printSourcesSuffix {cfg : Cfg} {env : Env} {all : List PrintArg}
    {origin : OriginId} {initial : St}
    (source : StmtSource cfg env (.print all origin) initial) (fuel offset : Nat)
    {args : List PrintArg} {state : St}
    (suffix : args = all.drop offset)
    {typingStart typingFinal : Nat}
    (typed : tyPrintArgs source.typingEnv args typingStart = .ok ((), typingFinal))
    {rootsStart rootsFinal : RState}
    (rooted : rpPrintArgs source.rootsEnv args rootsStart = .ok ((), rootsFinal))
    (effects : EffLe rootsFinal.eff source.world.E)
    (frame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
      (printSuffixFuture source.context args))
    (observed : ObservedSafe cfg.mod source.world
      (source.context.mayShrink source.world.ownerP source.observation) source.observation state.store)
    (classified : cfg.mod.profile = .shrink →
      ClassifiedParameters cfg.mod source.world.P source.world.D source.observation state.store)
    {results : List Ty}
    (metadata : SourceResults source.typingEnv source.rootsEnv results) :
    PrintSourceCursor (cfg := cfg) env fuel results args state := by
  induction args generalizing offset typingStart typingFinal rootsStart rootsFinal state with
  | nil => exact .nil
  | cons arg rest ih =>
      have hdrop : arg :: rest = all.drop offset := suffix
      have harg : all[offset]? = some arg := by
        have hfirst : (all.drop offset)[0]? = some arg := by rw [← hdrop]; rfl
        simpa using hfirst
      have hrest : rest = all.drop (offset + 1) := by
        have h := congrArg (fun xs : List PrintArg => xs.drop 1) hdrop
        simpa using h
      cases arg with
      | text text =>
          simp only [tyPrintArgs] at typed
          simp only [rpPrintArgs] at rooted
          refine .text (ih (offset + 1) hrest typed rooted effects ?_ observed classified)
          simpa [printSuffixFuture, PrintArg.variables] using frame
      | expr expr =>
          simp only [tyPrintArgs] at typed
          inv at typed
          simp only [rpPrintArgs] at rooted
          inv at rooted
          obtain ⟨ty, typingNext, htypedExpr, htypedRest⟩ := typed
          obtain ⟨roots, rootsNext, hrootedExpr, hrootedRest⟩ := rooted
          have hty : ((∃ t, ty = .int t) ∨ ty = .bool) ∧
              tyPrintArgs source.typingEnv rest typingNext = .ok ((), typingFinal) := by
            cases ty <;> inv at htypedRest <;> first
              | exact ⟨Or.inl ⟨_, rfl⟩, htypedRest⟩
              | exact ⟨Or.inr rfl, htypedRest⟩
          have childAt : (DemandNode.statement (.print all origin)).child? offset =
              some (.expression expr) := by
            simp [DemandNode.child?, DemandNode.children, harg]
          have visible : ∀ x, x ∈ source.typingEnv.visible ↔
              x ∈ (DemandNode.statement (.print all origin)).visibleForChild
                source.typingEnv.visible offset := by
            intro x
            simp [DemandNode.visibleForChild]
          have phase : DemandNodeHasPhase (.expression expr) .expression := by
            simp [DemandNodeHasPhase, DemandNode.phaseMatches]
          let childContext := source.context.child rfl offset (.expression expr) .expression childAt phase
          have childInputEq : childContext.inputFuture = expr.variables ++ childContext.outputFuture := by
            cases childContext with
            | pilot profile active => rfl
            | shrink profile context => rfl
          have childFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
              state childContext.inputFuture := by
            cases hcontext : source.context with
            | pilot profile active =>
                have base : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
                    state (expr.variables ++ (rest.flatMap PrintArg.variables ++ active)) := by
                  simpa [hcontext, printSuffixFuture, EvaluationContext.outputFuture,
                    DemandNode.visibleAfter, PrintArg.variables, List.append_assoc] using frame
                have houtput : childContext.outputFuture = active := by
                  simp [childContext, hcontext, EvaluationContext.child, EvaluationContext.outputFuture,
                    DemandNode.visibleForChild, DemandNode.visibleAfter]
                have hinput : childContext.inputFuture = expr.variables ++ active := by
                  rw [childInputEq, houtput]
                apply base.narrowFuture
                intro x hx
                rw [hinput] at hx
                simp only [List.mem_append] at hx ⊢
                rcases hx with hx | hx
                · exact Or.inl hx
                · exact Or.inr (Or.inr hx)
            | shrink profile context =>
                have hout := printShrinkExprOutputFuture profile context offset expr rest harg hrest
                have base : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
                    state (expr.variables ++ (rest.flatMap PrintArg.variables ++ context.outputFuture)) := by
                  change Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
                    (expr.variables ++ (rest.flatMap PrintArg.variables ++
                      (EvaluationContext.shrink profile context).outputFuture))
                  simpa [hcontext, printSuffixFuture, PrintArg.variables, List.append_assoc] using frame
                have houtput : childContext.outputFuture =
                    rest.flatMap PrintArg.variables ++ (EvaluationContext.shrink profile context).outputFuture := by
                  simpa [childContext, hcontext, phase, printSuffixFuture] using hout
                have hinput : childContext.inputFuture =
                    expr.variables ++ (rest.flatMap PrintArg.variables ++
                      (EvaluationContext.shrink profile context).outputFuture) := by
                  rw [childInputEq, houtput]
                rw [hinput]
                exact base
          have effectsExpr : EffLe rootsNext.eff source.world.E :=
            ((rpPrintArgs_mono hrootedRest).2.trans effects)
          obtain ⟨child, hTypingEnv, hRootsEnv, hChildTy, hWorld, hObservation,
              hChildFuture, hRetained, hMayShrink, _⟩ := source.expressionChildSource offset expr
                childAt visible typingStart typingNext ty rootsStart rootsNext roots
                htypedExpr hrootedExpr effectsExpr childFrame observed classified
          have childMetadata : SourceResults child.typingEnv child.rootsEnv results := by
            rw [hTypingEnv, hRootsEnv]
            exact metadata
          have childPrintable : (∃ t, child.ty = .int t) ∨ child.ty = .bool := by
            rw [hChildTy]
            exact hty.1
          refine .expr child childPrintable childMetadata ?_
          intro part final doneArg
          obtain ⟨value, after, heval, hrender, hfinal⟩ := execPrintExpr_success doneArg
          subst final
          let result := child.result fuel value heval
          have hchildContext : child.context.outputFuture = childContext.outputFuture := by
            simpa [childContext, phase] using hChildFuture
          have nextFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
              after (printSuffixFuture source.context rest) := by
            cases hcontext : source.context with
            | pilot profile active =>
                have hactive := source.active
                rw [hcontext] at hactive
                have hactivePilot : ∀ x, x ∈ source.typingEnv.visible ↔ x ∈ active := by
                  intro x
                  exact (hactive x).symm
                have houtput : childContext.outputFuture = active := by
                  simp [childContext, hcontext, EvaluationContext.child, EvaluationContext.outputFuture,
                    DemandNode.visibleForChild, DemandNode.visibleAfter]
                have hframe := result.frame
                rw [hchildContext, houtput] at hframe
                have activeFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv
                    source.rootsEnv env after active := by
                  rw [hWorld, hTypingEnv, hRootsEnv] at hframe
                  exact hframe
                apply activeFrame.changeFuture
                intro x hxvisible _
                exact hactivePilot x |>.1 hxvisible
            | shrink profile context =>
                have hout := printShrinkExprOutputFuture profile context offset expr rest harg hrest
                have hout' : childContext.outputFuture = printSuffixFuture source.context rest := by
                  simpa [childContext, hcontext, phase] using hout
                have hframe := result.frame
                rw [hchildContext, hout'] at hframe
                rw [hWorld, hTypingEnv, hRootsEnv] at hframe
                simpa [hcontext] using hframe
          have nextObserved : ObservedSafe cfg.mod source.world
              (source.context.mayShrink source.world.ownerP source.observation) source.observation
              after.store := by
            simpa [hWorld, hObservation, hMayShrink] using result.observed
          have nextClassified : cfg.mod.profile = .shrink →
              ClassifiedParameters cfg.mod source.world.P source.world.D source.observation after.store := by
            simpa [hWorld, hObservation] using result.classified
          exact ih (offset + 1) hrest hty.2 hrootedRest effects nextFrame
            nextObserved nextClassified

theorem StmtSource.printSourceCursor {cfg : Cfg} {env : Env} {args : List PrintArg}
    {origin : OriginId} {state : St}
    (source : StmtSource cfg env (.print args origin) state) (fuel : Nat)
    {results : List Ty}
    (metadata : SourceResults source.typingEnv source.rootsEnv results) :
    PrintSourceCursor (cfg := cfg) env fuel results args state := by
  have typedStmt := source.typed
  simp only [tyStmt] at typedStmt
  inv at typedStmt
  obtain ⟨_, htypedExists⟩ := typedStmt
  obtain ⟨typingFinal, htyped, _, _⟩ := htypedExists
  have rootedStmt := source.rooted
  simp only [rpStmt] at rootedStmt
  inv at rootedStmt
  obtain ⟨rootsFinal, hrooted, houtputs⟩ := rootedStmt
  have effects : EffLe rootsFinal.eff source.world.E :=
    (PMono.noteOutputs _ _ _ houtputs).2.trans source.effects
  have frame := printSuffixFrame source
  exact printSourcesSuffix source fuel 0 rfl htyped hrooted effects frame source.observed
    source.classified metadata

end Goose.Lower
