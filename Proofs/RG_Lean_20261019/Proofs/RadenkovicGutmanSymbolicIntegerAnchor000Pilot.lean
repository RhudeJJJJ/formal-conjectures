/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanCompactIntegerAnchor000Source
namespace Gebendorfer.RadenkovicGutman.SymbolicIntegerAnchor000Pilot
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1/268435456)
  b := (1153433/281474976710656)
  s := [(4398046511099/4398046511104),(1/4398046511104),(-1/2199023255552)]
  L := [(403781975247/604462909807314587353088),(1938142390991/14507109835375550096474112),(48453282499/7253554917687775048237056),(1/226673591177742970257408),(-1/453347182355485940514816)]
  c := (403781975247/604462909807314587353088)
  R := (-1401724318011501/100000000000000)
  total := (-650471/125000000000000)
  k := 41
  n := 32
  sFloor := (2199023255549/4398046511104)
  nFloor := (121866014031/154742504910672534362390528)
  eFloor := (91128537667/154742504910672534362390528)
}

#check "COMPACT_WITNESS_READY"
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1048576,width:=104857,den:=281474976710656,localDen:=14507109835375550096474112,lowerC:=9690767405928,s:=[14507109835359057422057472,3298534883328,-6597069766656],L:=[9690767405928,1938142390991,96906564998,64,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (CompactIntegerAnchor000Source.source.poly i) 1048576 104857 281474976710656
}
set_option profiler true
set_option profiler.threshold 10
theorem checked : IntegerPolynomialPaymentCell.checks CompactIntegerAnchor000Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 9)
        (CoreQuotient.fused G u 9 9) ((51/26 : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 9 CompactLiteralAnchor000Base.data
    CompactLiteralAnchor000Base.path_checked CompactLiteralAnchor000Base.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry CompactIntegerAnchor000Source.source_checked checked)
    budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.SymbolicIntegerAnchor000Pilot
