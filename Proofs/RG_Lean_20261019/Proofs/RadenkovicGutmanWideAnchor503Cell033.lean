/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor503Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor503Cell033
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (420027/274877906944)
  b := (15751/8589934592)
  s := [(4398046497313/4398046511104),(-345/274877906944),(-137/1099511627776)]
  L := [(69346044822345870739245009/41538374868278621028243970633760768),(4730216976599/7083549724304467820544),(236509717313/3541774862152233910272),(-125/442721857769029238784),(-5/221360928884514619392)]
  c := (246366642011/147573952589676412928)
  R := (-126317340122027/12500000000000)
  total := (-1529823007/500000000000000)
  k := 30
  n := 32
  sFloor := (1099511622811/2199023255552)
  nFloor := (1912217968949/9444732965739290427392)
  eFloor := (448963331155/2361183241434822606848)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=420027,width:=84005,den:=274877906944,localDen:=124615124604835863084731911901282304,lowerC:=208038134466986247242907648,s:=[124615124214078926093200249048793088,-156404777912642649477611520,-15527140995675393462632448],L:=[208038134467037612217735027,83214857082784572646621184,8321445896565063644348416,-35184372088832000,-2814749767106560],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor503Source.source.poly i) 420027 84005 274877906944
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
end Gebendorfer.RadenkovicGutman.WideAnchor503Cell033
