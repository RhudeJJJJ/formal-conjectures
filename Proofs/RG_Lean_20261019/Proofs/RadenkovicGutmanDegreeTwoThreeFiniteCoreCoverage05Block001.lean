/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreRepair05At008
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreRepair05At010
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreRepair05At012
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreRepair05At014
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys.CoreCoverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked5b001 : coveredRange 5 8 8=true := by
  rw [coveredRange,decide_eq_true_eq]
  intro i
  have hi := i.isLt
  by_cases h0 : 8+i.val < 10
  · have h := of_decide_eq_true checkedRepair5At008 (⟨8+i.val-8,by omega⟩ : Fin 2)
    have he : 8+(8+i.val-8)=8+i.val := by omega
    dsimp only [Fin.val_mk] at h
    rw [he] at h
    exact h
  ·
    by_cases h1 : 8+i.val < 12
    · have h := of_decide_eq_true checkedRepair5At010 (⟨8+i.val-10,by omega⟩ : Fin 2)
      have he : 10+(8+i.val-10)=8+i.val := by omega
      dsimp only [Fin.val_mk] at h
      rw [he] at h
      exact h
    ·
      by_cases h2 : 8+i.val < 14
      · have h := of_decide_eq_true checkedRepair5At012 (⟨8+i.val-12,by omega⟩ : Fin 2)
        have he : 12+(8+i.val-12)=8+i.val := by omega
        dsimp only [Fin.val_mk] at h
        rw [he] at h
        exact h
      ·
        have h := of_decide_eq_true checkedRepair5At014 (⟨8+i.val-14,by omega⟩ : Fin 2)
        have he : 14+(8+i.val-14)=8+i.val := by omega
        dsimp only [Fin.val_mk] at h
        rw [he] at h
        exact h
#print axioms checked5b001
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys.CoreCoverage
