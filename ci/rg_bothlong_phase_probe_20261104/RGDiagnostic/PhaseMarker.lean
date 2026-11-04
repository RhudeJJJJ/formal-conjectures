import Lean

/-! Diagnostic commands only. No RG declarations, proof exports, or receipts. -/
namespace RGDiagnosticPhaseMarker
open Lean Elab Command

private def appendPhase (label : String) : IO Unit := do
  let some path ← IO.getEnv "RG_PHASE_LOG"
    | throw <| IO.userError "RG_PHASE_LOG must name a separate diagnostic file"
  let stamp ← IO.monoMsNow
  let handle ← IO.FS.Handle.mk (System.FilePath.mk path) .append
  handle.putStrLn s!"RG_PHASE\t{stamp}\t{label}"
  handle.flush

elab "rg_phase " label:str : command => do
  liftIO <| appendPhase label.getString

elab "rg_phase_checked " label:str decl:ident : command => do
  let env ← getEnv
  unless (env.checked.get.find? decl.getId).isSome do
    throwError "Diagnostic checkpoint expected kernel-checked declaration {decl}"
  liftIO <| appendPhase label.getString

end RGDiagnosticPhaseMarker
