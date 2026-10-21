/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreRepair04At000
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreRepair04At002
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreRepair04At004
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreRepair04At006
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys.CoreCoverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked4b000 : coveredRange 4 0 8=true := by
  rw [coveredRange,decide_eq_true_eq]
  intro i
  have hi := i.isLt
  by_cases h0 : 0+i.val < 2
  · have h := of_decide_eq_true checkedRepair4At000 (⟨0+i.val-0,by omega⟩ : Fin 2)
    have he : 0+(0+i.val-0)=0+i.val := by omega
    dsimp only [Fin.val_mk] at h
    rw [he] at h
    exact h
  ·
    by_cases h1 : 0+i.val < 4
    · have h := of_decide_eq_true checkedRepair4At002 (⟨0+i.val-2,by omega⟩ : Fin 2)
      have he : 2+(0+i.val-2)=0+i.val := by omega
      dsimp only [Fin.val_mk] at h
      rw [he] at h
      exact h
    ·
      by_cases h2 : 0+i.val < 6
      · have h := of_decide_eq_true checkedRepair4At004 (⟨0+i.val-4,by omega⟩ : Fin 2)
        have he : 4+(0+i.val-4)=0+i.val := by omega
        dsimp only [Fin.val_mk] at h
        rw [he] at h
        exact h
      ·
        have h := of_decide_eq_true checkedRepair4At006 (⟨0+i.val-6,by omega⟩ : Fin 2)
        have he : 6+(0+i.val-6)=0+i.val := by omega
        dsimp only [Fin.val_mk] at h
        rw [he] at h
        exact h
#print axioms checked4b000
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys.CoreCoverage
