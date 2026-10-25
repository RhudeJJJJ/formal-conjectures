/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor020Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor020Cell032
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (700045/549755813888)
  b := (420027/274877906944)
  s := [(4398046072961/4398046511104),(-175257/4398046511104),(-8763/2199023255552)]
  L := [(191812359106520888272286811/2596148429267413814265248164610048),(817745186485/27670116110564327424),(81774485135/27670116110564327424),(-1687/6917529027641081856),(-5/432345564227567616)]
  c := (1362908783921/18446744073709551616)
  R := (-821038860622751/100000000000000)
  total := (-2067108493/1000000000000000)
  k := 24
  n := 32
  sFloor := (2199022940089/4398046511104)
  nFloor := (462458714885/2361183241434822606848)
  eFloor := (1247130100181/9444732965739290427392)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=700045,width:=140009,den:=549755813888,localDen:=7788445287802241442795744493830144,lowerC:=575437077319367948463243264,s:=[7788444511900309728812633419677696,-310360418508107029206269952,-31036573117040025755713536],L:=[575437077319562664816860433,230174807321116422606684160,23017471298900010268098560,-1899393142843506688,-90071992547409920],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor020Source.source.poly i) 700045 140009 549755813888
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor020Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 29) (CoreQuotient.fused G u 9 29) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 29 WideAnchor020Source.data
    WideAnchor020Source.path_checked WideAnchor020Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor020Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 29 9) (CoreQuotient.fused G u 29 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 29 9 WideAnchor020Source.data
    WideAnchor020Source.path_swapped WideAnchor020Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor020Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor020Cell032
