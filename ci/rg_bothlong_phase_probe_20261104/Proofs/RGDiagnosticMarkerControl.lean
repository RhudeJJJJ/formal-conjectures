import Proofs.RGDiagnosticPhaseMarker
rg_phase "control.header.complete"
namespace RGDiagnosticMarkerControl
theorem checked : True := True.intro
end RGDiagnosticMarkerControl
rg_phase_checked "control.kernel.checked" RGDiagnosticMarkerControl.checked
#print axioms RGDiagnosticMarkerControl.checked
rg_phase "control.axioms.complete"
