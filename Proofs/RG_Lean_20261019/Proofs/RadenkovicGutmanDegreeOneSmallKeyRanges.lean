/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def coveredRange (n start count : ℕ) : Bool :=
  decide (∀ i : Fin count, ∀ p q : Fin 11,
    eligible n (start+i.val) p.val q.val=true →
      (⟨n,start+i.val,p.val,q.val⟩ : Key) ∈ keys)

theorem range_sound (n start count : ℕ) (hc : coveredRange n start count=true)
    (i : ℕ) (p q : Fin 11) (hlo : start≤i) (hhi : i<start+count)
    (he : eligible n i p.val q.val=true) : (⟨n,i,p.val,q.val⟩ : Key) ∈ keys := by
  have hk := of_decide_eq_true hc (⟨i-start,by omega⟩ : Fin count) p q
  have hi : start+(i-start)=i := by omega
  dsimp only [Fin.val_mk] at hk
  rw [hi] at hk
  exact hk he

#print axioms range_sound
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
