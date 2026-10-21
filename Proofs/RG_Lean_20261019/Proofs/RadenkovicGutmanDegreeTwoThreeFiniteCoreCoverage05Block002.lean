/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreRepair05At016
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreRepair05At018
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys.CoreCoverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked5b002 : coveredRange 5 16 4=true := by
  rw [coveredRange,decide_eq_true_eq]
  intro i
  have hi := i.isLt
  by_cases h0 : 16+i.val < 18
  · have h := of_decide_eq_true checkedRepair5At016 (⟨16+i.val-16,by omega⟩ : Fin 2)
    have he : 16+(16+i.val-16)=16+i.val := by omega
    dsimp only [Fin.val_mk] at h
    rw [he] at h
    exact h
  ·
    have h := of_decide_eq_true checkedRepair5At018 (⟨16+i.val-18,by omega⟩ : Fin 2)
    have he : 18+(16+i.val-18)=16+i.val := by omega
    dsimp only [Fin.val_mk] at h
    rw [he] at h
    exact h
#print axioms checked5b002
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys.CoreCoverage
