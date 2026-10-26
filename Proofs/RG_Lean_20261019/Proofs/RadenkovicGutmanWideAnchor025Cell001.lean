/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor025Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor025Cell001
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1258291/281474976710656)
  b := (1509949/281474976710656)
  s := [(4398046511101/4398046511104),(1/4398046511104),(-1/2199023255552)]
  L := [(5005431243147/19342813113834066795298816),(6006512718251/58028439341502200385896448),(100108465721/9671406556917033397649408),(13/3626777458843887524118528),(-1/604462909807314587353088)]
  c := (625678905393/2417851639229258349412352)
  R := (-181142615497407/12500000000000)
  total := (-6436257/500000000000000)
  k := 42
  n := 32
  sFloor := (1099511627775/2199023255552)
  nFloor := (1253130095523/618970019642690137449562112)
  eFloor := (144074230809/77371252455336267181195264)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1258291,width:=251658,den:=281474976710656,localDen:=58028439341502200385896448,lowerC:=15016293729432,s:=[58028439341462617967296512,13194139533312,-26388279066624],L:=[15016293729441,6006512718251,600650794326,208,-96],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor025Source.source.poly i) 1258291 251658 281474976710656
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor025Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 34) (CoreQuotient.fused G u 9 34) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 34 WideAnchor025Source.data
    WideAnchor025Source.path_checked WideAnchor025Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor025Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 34 9) (CoreQuotient.fused G u 34 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 34 9 WideAnchor025Source.data
    WideAnchor025Source.path_swapped WideAnchor025Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor025Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor025Cell001
