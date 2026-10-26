/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor538Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor538Cell080
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1080087/134217728)
  b := (162013/16777216)
  s := [(1894133129619/4398046511104),(-140914663195/2199023255552),(9257592367/1099511627776)]
  L := [(121413400793441308215/295147905179352825856),(575257139845/8796093022208),(-96195695327/13194139533312),(36737713/68719476736),(-10392715/824633720832)]
  c := (452300164079/1099511627776)
  R := (-44413767310091/100000000000000)
  total := (-329018151003/500000000000000)
  k := 2
  n := 32
  sFloor := (1649334172697/8796093022208)
  nFloor := (472885165241/140737488355328)
  eFloor := (914906956113/281474976710656)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1080087,width:=216017,den:=134217728,localDen:=885443715538058477568,lowerC:=364240202380263555072,s:=[381339367780487528448,-56739737807754362880,7455198085493293056],L:=[364240202380323924645,57907279744330629120,-6455583835085078528,473361827594502144,-11159092760412160],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor538Source.source.poly i) 1080087 216017 134217728
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor538Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 16) (CoreQuotient.fused G u 5 16) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 16 WideAnchor538Source.data
    WideAnchor538Source.path_checked WideAnchor538Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor538Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 16 5) (CoreQuotient.fused G u 16 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 16 5 WideAnchor538Source.data
    WideAnchor538Source.path_swapped WideAnchor538Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor538Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor538Cell080
