/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor265Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor265Cell097
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (748837/4194304)
  b := (224651/1048576)
  s := [(551775356639/1099511627776),(-300663027565/8796093022208),(5703470205/4398046511104)]
  L := [(276551270227855361231/590295810358705651712),(831440728423/13194139533312),(-465791947/824633720832),(-78068057/412316860416),(4277983/206158430208)]
  c := (1030233764007/2199023255552)
  R := (-37911377759577/100000000000000)
  total := (-387340791733/31250000000000)
  k := 2
  n := 32
  sFloor := (1031236691489/4398046511104)
  nFloor := (808732008139/1073741824)
  eFloor := (143148768415/268435456)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=748837,width:=149767,den:=4194304,localDen:=1770887431076116955136,lowerC:=829653810683446296576,s:=[888696416813715554304,-60531462680063508480,2296520437892382720],L:=[829653810683566083693,111594085535600082944,-1000280589552582656,-335299751677263872,36747594155687936],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor265Source.source.poly i) 748837 149767 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor265Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 41) (CoreQuotient.fused G u 0 41) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 41 WideAnchor265Source.data
    WideAnchor265Source.path_checked WideAnchor265Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor265Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 41 0) (CoreQuotient.fused G u 41 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 41 0 WideAnchor265Source.data
    WideAnchor265Source.path_swapped WideAnchor265Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor265Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor265Cell097
