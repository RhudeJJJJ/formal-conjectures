/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor503Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor503Cell032
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (700045/549755813888)
  b := (420027/274877906944)
  s := [(2199023250763/2199023255552),(-3831/4398046511104),(-191/2199023255552)]
  L := [(1368703569073/1180591620717411303424),(3284888553001/7083549724304467820544),(82122212533/1770887431076116955136),(-61/442721857769029238784),(-1/110680464442257309696)]
  c := (1368703569073/1180591620717411303424)
  R := (-1028770876569939/100000000000000)
  total := (-2596149769/1000000000000000)
  k := 30
  n := 32
  sFloor := (137438953041/274877906944)
  nFloor := (165991143105/1180591620717411303424)
  eFloor := (1247120364073/9444732965739290427392)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=700045,width:=140009,den:=549755813888,localDen:=7083549724304467820544,lowerC:=8212221414438,s:=[7083549708878019035136,-6170257391616,-615254065152],L:=[8212221414438,3284888553001,328488850132,-976,-64],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor503Source.source.poly i) 700045 140009 549755813888
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor503Source.source witness geometry=true := by
  unfold IntegerPolynomialPaymentCell.checks
  rw [decide_eq_true_eq]
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by intro i; rfl,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩
theorem budget : SemanticPolynomialPaymentCell.Budget witness := by
  unfold SemanticPolynomialPaymentCell.Budget
  decide +kernel
theorem logarithm_checked : RationalLog.accepts witness.c witness.R witness.k witness.n=true := by decide +kernel
noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 33) (CoreQuotient.fused G u 4 33) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 33 WideAnchor503Source.data
    WideAnchor503Source.path_checked WideAnchor503Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor503Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 33 4) (CoreQuotient.fused G u 33 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 33 4 WideAnchor503Source.data
    WideAnchor503Source.path_swapped WideAnchor503Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor503Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor503Cell032
