/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor013Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor013Cell096
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (624031/4194304)
  b := (748837/4194304)
  s := [(2471247214263/8796093022208),(39265679191/17592186044416),(-17493705543/8796093022208)]
  L := [(781160795269815181889/1180591620717411303424),(37342678989/4398046511104),(4677677309/1649267441664),(-6443803/68719476736),(-4919017/206158430208)]
  c := (727512683039/1099511627776)
  R := (-20649497641357/100000000000000)
  total := (-188406941097/31250000000000)
  k := 1
  n := 32
  sFloor := (1235623607131/8796093022208)
  nFloor := (1073197953167/34359738368)
  eFloor := (455237068525/17179869184)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=624031,width:=124806,den:=4194304,localDen:=3541774862152233910272,lowerC:=2343482385808289169408,s:=[995055559274127163392,7905225374089347072,-7043896236847398912],L:=[2343482385809445545667,30072297188021501952,10045235531698143232,-332111077762400256,-84508068573872128],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor013Source.source.poly i) 624031 124806 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor013Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 22) (CoreQuotient.fused G u 9 22) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 22 WideAnchor013Source.data
    WideAnchor013Source.path_checked WideAnchor013Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor013Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 22 9) (CoreQuotient.fused G u 22 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 22 9 WideAnchor013Source.data
    WideAnchor013Source.path_swapped WideAnchor013Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor013Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor013Cell096
