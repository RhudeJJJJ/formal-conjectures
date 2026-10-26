/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor545Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor545Cell123
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (669709/32768)
  b := (1607301/65536)
  s := [(8358997497923/144115188075855872),(-4765553321873/144115188075855872),(629131170447/72057594037927936)]
  L := [(593028819123494995945/590295810358705651712),(-2988435397/1649267441664),(36194321/68719476736),(-26117899/206158430208),(83455/4294967296)]
  c := (17235486581/17179869184)
  R := (161606481123/100000000000000)
  total := (7897456613341/1000000000000000)
  k := 0
  n := 32
  sFloor := (303231657309/18014398509481984)
  nFloor := 1718720562849335599478740682906679107195387309848190467369255846609289273797911773184
  eFloor := 1710601259684108339902730486504596572130383427112193213388417434999159441444879466496
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1339418,width:=267883,den:=65536,localDen:=1770887431076116955136,lowerC:=1776620428705004519424,s:=[102715361254477824,-58559119219175424,15461527644905472],L:=[1779086457370484987835,-3208808074080944128,932720549975556096,-224351044090462208,34409903586017280],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor545Source.source.poly i) 1339418 267883 65536
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor545Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 23) (CoreQuotient.fused G u 5 23) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 23 WideAnchor545Source.data
    WideAnchor545Source.path_checked WideAnchor545Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor545Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 23 5) (CoreQuotient.fused G u 23 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 23 5 WideAnchor545Source.data
    WideAnchor545Source.path_swapped WideAnchor545Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor545Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor545Cell123
