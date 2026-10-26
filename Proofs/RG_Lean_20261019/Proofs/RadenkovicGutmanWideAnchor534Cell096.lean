/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor534Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor534Cell096
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (624031/4194304)
  b := (748837/4194304)
  s := [(64936457303/274877906944),(244794096405/35184372088832),(-38667664197/17592186044416)]
  L := [(26517882988270821859045/37778931862957161709568),(37211980259/6597069766656),(7297623819/2199023255552),(-173037425/412316860416),(4497117/137438953472)]
  c := (385885985281/549755813888)
  R := (-2212076587363/12500000000000)
  total := (-1036997488823/200000000000000)
  k := 1
  n := 32
  sFloor := (64936457303/549755813888)
  nFloor := (1034495824789/274877906944)
  eFloor := (113816712831/34359738368)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=624031,width:=124806,den:=4194304,localDen:=113336795588871485128704,lowerC:=79553648964798353768448,s:=[26774396201710594818048,788536978735009628160,-249114529708237651968],L:=[79553648964812465577135,639296952927210438656,376116667693387481088,-47564165206979379200,3708474324726841344],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor534Source.source.poly i) 624031 124806 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor534Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 12) (CoreQuotient.fused G u 5 12) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 12 WideAnchor534Source.data
    WideAnchor534Source.path_checked WideAnchor534Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor534Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 12 5) (CoreQuotient.fused G u 12 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 12 5 WideAnchor534Source.data
    WideAnchor534Source.path_swapped WideAnchor534Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor534Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor534Cell096
