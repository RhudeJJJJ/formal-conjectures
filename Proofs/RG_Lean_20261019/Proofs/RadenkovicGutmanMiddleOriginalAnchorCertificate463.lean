/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanMiddleOriginalAnchorPredicate
import Proofs.RadenkovicGutmanWideAnchor463OriginalAnchor
namespace Gebendorfer.RadenkovicGutman.MiddleOriginalAnchorCertificate463
open CoreQuotient ActualFusionIntegral OriginalAssembly DegreeOneMiddleAnchors
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def anchor : Anchor := ⟨52,3,38,(3991683535660615432113460817404497/32624163332060752803334972325527552)⟩
theorem certificate : MiddleOriginalAnchorPredicate.Proved anchor := by
  intro m C u r s _hT hd hor hN
  rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have hn : Fintype.card (Fin m)+3+38+2≤52 := by
      simp only [order,Fintype.card_sum,Fintype.card_fin,anchor] at hN ⊢
      omega
    have hb := WideAnchor463OriginalAnchor.actual_bound C u hd hn
    convert hb using 1 <;> norm_num [anchor,WideAnchor463OriginalAnchor.target]
  · have hn : Fintype.card (Fin m)+38+3+2≤52 := by
      simp only [order,Fintype.card_sum,Fintype.card_fin,anchor] at hN ⊢
      omega
    have hb := WideAnchor463OriginalAnchor.actual_bound_swapped C u hd hn
    convert hb using 1 <;> norm_num [anchor,WideAnchor463OriginalAnchor.target]
#print axioms certificate
end
end Gebendorfer.RadenkovicGutman.MiddleOriginalAnchorCertificate463
