import Goose.Lower.SourceDivergence

namespace Goose.Lower.SourceDivergenceChecks

open Goose.Core Goose.Lower.SourceDivergence

def returningBody : Block := .mk 0 [.while (.bool true)
  (.mk 1 [.ifS (.bool false) (.mk 2 [.ret (some (.lit .i64 1)) 0] none)
    (some (.mk 3 [.while (.bool true)
      (.mk 4 [.ret (some (.lit .i64 9)) 0] none) 0] none)) 0] none) 0] none

def normalCallBody : Block := .mk 0 [.expr (.call 0 [] 0) 0, .expr (.call 1 [] 0) 0] none

def abortCallBody : Block := .mk 0 [.expr (.call 2 [] 0) 0] none

def sourceModule : Module :=
  { files := #["source-divergence.goose"], types := #[.int .i64], globals := #[],
    impls := #[
      { name := "returning", params := #[], results := #[.int .i64], vars := #[],
        body := returningBody, summary := .unknown },
      { name := "normalResult", params := #[], results := #[.int .i64], vars := #[],
        body := .mk 0 [] (some (.lit .i64 7)), summary := .unknown },
      { name := "aborting", params := #[], results := #[], vars := #[],
        body := .mk 0 [.abort "stop" 0] none, summary := .unknown },
      { name := "main", params := #[], results := #[], vars := #[],
        body := normalCallBody, summary := .unknown }],
    contexts := #[⟨0, "returning", [], [[]], []⟩, ⟨1, "normalResult", [], [[]], []⟩,
      ⟨2, "aborting", [], [], []⟩, ⟨3, "main", [], [], []⟩],
    entry := 3, origins := #[⟨0, 1, "source-divergence"⟩] }

def sourceEnv : Env := ⟨#[], 0, [], 0⟩

theorem normal_call_nondivergence (n : Nat) (state final : St) (value : Val)
    (h : execBlock n ⟨.release, sourceModule⟩ sourceEnv [] normalCallBody state =
      .ok (.normal value) final) : normalCallBody.diverges sourceModule.noReturn = false :=
  normalBlock_diverges_false n ⟨.release, sourceModule⟩ sourceEnv [] normalCallBody
    state final value h

theorem returning_body_excludes_normal (n : Nat) (state final : St) (value : Val) :
    execBlock n ⟨.release, sourceModule⟩ sourceEnv [] returningBody state ≠
      .ok (.normal value) final := by
  intro h
  have hd := normalBlock_diverges_false n ⟨.release, sourceModule⟩ sourceEnv [] returningBody
    state final value h
  change true = false at hd
  cases hd

theorem abort_call_excludes_normal (n : Nat) (state final : St) (value : Val) :
    execBlock n ⟨.release, sourceModule⟩ sourceEnv [] abortCallBody state ≠
      .ok (.normal value) final := by
  intro h
  have hd := normalBlock_diverges_false n ⟨.release, sourceModule⟩ sourceEnv [] abortCallBody
    state final value h
  change true = false at hd
  cases hd

#guard match execBlock 40 ⟨.release, sourceModule⟩ sourceEnv [] normalCallBody St.initial with
  | .ok (.normal .unit) _ => true
  | _ => false
#guard match validate sourceModule with | .ok _ => true | _ => false
#guard sourceModule.noReturn 0 = false
#guard sourceModule.noReturn 1 = false
#guard sourceModule.noReturn 2 = true
#guard returningBody.hasBreak = false
#guard match execBlock 40 ⟨.release, sourceModule⟩ sourceEnv [] returningBody St.initial with
  | .ok (.ret (.int .i64 9)) _ => true
  | _ => false
#guard match execBlock 40 ⟨.release, sourceModule⟩ sourceEnv [] abortCallBody St.initial with
  | .stop (.abort .userAbort 0) _ => true
  | _ => false
#guard match eval 40 .release sourceModule with | .done .returned "" => true | _ => false

end Goose.Lower.SourceDivergenceChecks
