/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanMiddleOriginalAnchorPredicate
import Proofs.RadenkovicGutmanWideAnchor515OriginalAnchor
namespace Gebendorfer.RadenkovicGutman.MiddleOriginalAnchorCertificate515
open CoreQuotient ActualFusionIntegral OriginalAssembly DegreeOneMiddleAnchors
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def anchor : Anchor := ⟨52,4,4,(1246682777849720258451426429711833/32624163332060752803334972325527552)⟩
theorem certificate : MiddleOriginalAnchorPredicate.Proved anchor := by
  intro m C u r s _hT hd hor hN
  rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have hn : Fintype.card (Fin m)+4+4+2≤52 := by
      simp only [order,Fintype.card_sum,Fintype.card_fin,anchor] at hN ⊢
      omega
    have hb := WideAnchor515OriginalAnchor.actual_bound C u hd hn
    convert hb using 1 <;> norm_num [anchor,WideAnchor515OriginalAnchor.target]
  · have hn : Fintype.card (Fin m)+4+4+2≤52 := by
      simp only [order,Fintype.card_sum,Fintype.card_fin,anchor] at hN ⊢
      omega
    have hb := WideAnchor515OriginalAnchor.actual_bound C u hd hn
    convert hb using 1 <;> norm_num [anchor,WideAnchor515OriginalAnchor.target]
#print axioms certificate
end
end Gebendorfer.RadenkovicGutman.MiddleOriginalAnchorCertificate515
