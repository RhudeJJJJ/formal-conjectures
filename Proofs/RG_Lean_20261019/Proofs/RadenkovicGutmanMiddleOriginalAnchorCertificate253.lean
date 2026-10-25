/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanMiddleOriginalAnchorPredicate
import Proofs.RadenkovicGutmanWideAnchor253OriginalAnchor
namespace Gebendorfer.RadenkovicGutman.MiddleOriginalAnchorCertificate253
open CoreQuotient ActualFusionIntegral OriginalAssembly DegreeOneMiddleAnchors
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def anchor : Anchor := ⟨52,0,30,(2838255953706221856030762389061001/32624163332060752803334972325527552)⟩
theorem certificate : MiddleOriginalAnchorPredicate.Proved anchor := by
  intro m C u r s _hT hd hor hN
  rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have hn : Fintype.card (Fin m)+0+30+2≤52 := by
      simp only [order,Fintype.card_sum,Fintype.card_fin,anchor] at hN ⊢
      omega
    have hb := WideAnchor253OriginalAnchor.actual_bound C u hd hn
    convert hb using 1 <;> norm_num [anchor,WideAnchor253OriginalAnchor.target]
  · have hn : Fintype.card (Fin m)+30+0+2≤52 := by
      simp only [order,Fintype.card_sum,Fintype.card_fin,anchor] at hN ⊢
      omega
    have hb := WideAnchor253OriginalAnchor.actual_bound_swapped C u hd hn
    convert hb using 1 <;> norm_num [anchor,WideAnchor253OriginalAnchor.target]
#print axioms certificate
end
end Gebendorfer.RadenkovicGutman.MiddleOriginalAnchorCertificate253
