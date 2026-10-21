/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreRepair03At000
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreRepair03At002
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys.CoreCoverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked3b000 : coveredRange 3 0 4=true := by
  rw [coveredRange,decide_eq_true_eq]
  intro i
  have hi := i.isLt
  by_cases h0 : 0+i.val < 2
  · have h := of_decide_eq_true checkedRepair3At000 (⟨0+i.val-0,by omega⟩ : Fin 2)
    have he : 0+(0+i.val-0)=0+i.val := by omega
    dsimp only [Fin.val_mk] at h
    rw [he] at h
    exact h
  ·
    have h := of_decide_eq_true checkedRepair3At002 (⟨0+i.val-2,by omega⟩ : Fin 2)
    have he : 2+(0+i.val-2)=0+i.val := by omega
    dsimp only [Fin.val_mk] at h
    rw [he] at h
    exact h
#print axioms checked3b000
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys.CoreCoverage
