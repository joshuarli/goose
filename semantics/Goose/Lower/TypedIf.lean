import Goose.Lower.IfRuntime

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem typedStatementLoopSimulation_if_none {n : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {condition : Expr} {yes : Core.Block} {org : OriginId}
    (hcondition : TypedExprClaim n cfg results condition)
    (hyes : TypedBlockLoopSimulation n cfg results loop [] [] false yes) :
    TypedStatementLoopSimulation (n + 1) cfg results loop (.ifS condition yes none org) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter hgenerated hframes
  obtain ⟨child, htyping, hroots, _⟩ := source.ifConditionChild
  have hchild : SourceResults child.typingEnv child.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  apply stmt_if_none_loop_sim_at n loop condition yes org _ ls result ls' pt cfg env cx fr
    state hlow hpp hext hrel hcounter hgenerated hframes
  · intro id middle lowered point extended related
    exact hcondition env state child hchild ls middle id pt cx fr lowered point extended related
      hgir hresults hgenerated
  · intro after done middle id final point frame lowered pointAt extended related counter generatedBody framesBody
    obtain ⟨bodySource, bodyTyping, bodyRoots, _, _⟩ := source.ifThenChild n done
    have bodyMetadata : SourceResults bodySource.typingEnv bodySource.rootsEnv results := by
      rw [bodyTyping, bodyRoots]
      exact hmetadata
    have bodyLoops : LoopSourceMatches bodySource.typingEnv loop := by
      rw [bodyTyping]
      exact hloops
    exact hyes env after bodySource bodyMetadata bodyLoops middle final id point cx frame
      lowered pointAt extended related (by trivial) hgir hresults hdepth htargets counter generatedBody framesBody

theorem typedStatementLoopSimulation_if_some {n : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {condition : Expr} {yes no : Core.Block} {org : OriginId}
    (hcondition : TypedExprClaim n cfg results condition)
    (hyes : TypedBlockLoopSimulation n cfg results loop [] [] false yes)
    (hno : TypedBlockLoopSimulation n cfg results loop [] [] false no) :
    TypedStatementLoopSimulation (n + 1) cfg results loop (.ifS condition yes (some no) org) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter hgenerated hframes
  obtain ⟨child, htyping, hroots, _⟩ := source.ifConditionChild
  have hchild : SourceResults child.typingEnv child.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  apply stmt_if_some_loop_sim_at n loop condition yes no org _ ls result ls' pt cfg env cx fr
    state hlow hpp hext hrel hcounter hgenerated hframes
  · intro id middle lowered point extended related
    exact hcondition env state child hchild ls middle id pt cx fr lowered point extended related
      hgir hresults hgenerated
  · intro after done middle id final point frame lowered pointAt extended related counter generatedBody framesBody
    obtain ⟨bodySource, bodyTyping, bodyRoots, _, _⟩ := source.ifThenChild n done
    have bodyMetadata : SourceResults bodySource.typingEnv bodySource.rootsEnv results := by
      rw [bodyTyping, bodyRoots]
      exact hmetadata
    have bodyLoops : LoopSourceMatches bodySource.typingEnv loop := by
      rw [bodyTyping]
      exact hloops
    exact hyes env after bodySource bodyMetadata bodyLoops middle final id point cx frame
      lowered pointAt extended related (by trivial) hgir hresults hdepth htargets counter generatedBody framesBody
  · intro after done middle id final point frame lowered pointAt extended related counter generatedBody framesBody
    obtain ⟨bodySource, bodyTyping, bodyRoots, _, _⟩ := source.ifElseChild n done
    have bodyMetadata : SourceResults bodySource.typingEnv bodySource.rootsEnv results := by
      rw [bodyTyping, bodyRoots]
      exact hmetadata
    have bodyLoops : LoopSourceMatches bodySource.typingEnv loop := by
      rw [bodyTyping]
      exact hloops
    exact hno env after bodySource bodyMetadata bodyLoops middle final id point cx frame
      lowered pointAt extended related (by trivial) hgir hresults hdepth htargets counter generatedBody framesBody

end Goose.Lower
