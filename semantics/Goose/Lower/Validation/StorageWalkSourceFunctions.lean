import Goose.Lower.Validation.StorageWalkSource
import Goose.Lower.Validation.StorageWalkSourceParameters
import Goose.Lower.Validation.StorageWalkFlow
import Goose.Lower.Validation.StorageWalkControlTransfersFinish
import Goose.Lower.Validation.StorageWalkSourceInitial

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerImpl_storageWalkGraph {module : Core.Module} {impl : Core.Impl}
    (checked : Core.checkImpl module impl = .ok ()) : Nonempty (StorageWalkGraph (lowerImpl module impl)) := by
  let env := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun parameter => VTy.data (tyOfVar impl parameter.var)
  let parameters := (newBlock types env initState).1.2
  let initial := scopeInitialState env types
  let action := scopeImplTail impl parameters
  let slots := (lowerImpl module impl).slots
  obtain ⟨type, finish, bodySource, resultShape⟩ := (checkImpl_ok module impl checked).body
  have bodyAction := storageWalk_source_block impl.body (implEnv module impl) impl.results.toList []
    bodySource (storageWalk_impl_visible checked []) none
    ((impl.params.toList.zip parameters).map fun (parameter, value) =>
      (parameter.var, value, (impl.vars[parameter.var]?.map (·.org)).getD 0)) false
    (storageWalk_impl_pre_scopes checked parameters [])
  have actionFlow : StorageWalkAction slots [] none action := by
    unfold action scopeImplTail
    exact bodyAction.bind fun value => StorageWalkAction.finishFunction slots impl value
  obtain ⟨entry, exit, config, framed⟩ := actionFlow.preserves env initial
    (fun _ => []) (fun _ => []) (storageWalk_initial_configuration slots env types) trivial rfl
  have initialEntry : entry 0 = [] := (framed 0 (by rw [scopeInitialState_size]; decide)).1
  exact ⟨config.builder.finish initialEntry config.edges (lowerImpl module impl) rfl rfl⟩

theorem lowerContextAt_storageWalkGraph {module : Core.Module} {impl : Core.Impl}
    (checked : Core.checkImpl module impl = .ok ()) (context : Core.Context) :
    Nonempty (StorageWalkGraph (lowerContextAt module context impl)) := by
  obtain ⟨graph⟩ := lowerImpl_storageWalkGraph checked
  exact ⟨⟨graph.entry, graph.exit, graph.initial,
    by simpa only [lowerContextAt_slots, lowerContextAt_blocks] using graph.trace,
    by simpa only [lowerContextAt_blocks] using graph.edge⟩⟩

theorem lowerGlobal_storageWalkGraph {module : Core.Module} {index : GlobalId} {global : Core.Global}
    (checked : Core.checkGlobal module index global = .ok ()) :
    Nonempty (StorageWalkGraph (lowerGlobal module global).init) := by
  let env := lowerEnv module #[] [global.ty]
  let initial := scopeInitialState env []
  let action := scopeGlobalTail global
  let slots := (lowerGlobal module global).init.slots
  obtain ⟨descriptor, finish, source⟩ := checkGlobal_ok module index global checked
  have exprAction := storageWalk_source_expression global.init (initEnv module index) [global.ty] [] source
    (by intro variableId localVar member row; cases member) none
  have actionFlow : StorageWalkAction slots [] none action :=
    exprAction.bind fun value => StorageWalkAction.emitReturn slots none [value] (some global.org)
  obtain ⟨entry, exit, config, framed⟩ := actionFlow.preserves env initial
    (fun _ => []) (fun _ => []) (storageWalk_initial_configuration slots env []) trivial rfl
  have initialEntry : entry 0 = [] := (framed 0 (by rw [scopeInitialState_size]; decide)).1
  exact ⟨config.builder.finish initialEntry config.edges (lowerGlobal module global).init rfl rfl⟩

end Goose.Lower.Validation
