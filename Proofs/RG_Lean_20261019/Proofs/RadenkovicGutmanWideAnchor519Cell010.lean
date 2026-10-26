/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor519Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor519Cell010
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1623121/70368744177664)
  b := (60867/2199023255552)
  s := [(4398046511103/4398046511104)]
  L := [(1386050415913761334657496567/348449143727040986586495598010130648530944),(1477266620765/928455029464035206174343168),(18465764509/116056878683004400771792896),(-1/7253554917687775048237056),(1/14507109835375550096474112)]
  c := (615530034015/154742504910672534362390528)
  R := (-828951378280243/50000000000000)
  total := (-19012369/250000000000000)
  k := 48
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (34800216435/4835703278458516698824704)
  eFloor := (1782213862103/154742504910672534362390528)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1623121,width:=324623,den:=70368744177664,localDen:=1045347431181122959759486794030391945592832,lowerC:=4158151247737954091831132160,s:=[1045347431180885275271944001017611313741824],L:=[4158151247741284003972489701,1663254350701031457145487360,166324820323687460061052928,-144115188075855872,72057594037927936],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor519Source.source.poly i) 1623121 324623 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor519Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 4 4 WideAnchor519Source.data
    WideAnchor519Source.path_checked WideAnchor519Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor519Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 4 4 WideAnchor519Source.data
    WideAnchor519Source.path_swapped WideAnchor519Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor519Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor519Cell010
