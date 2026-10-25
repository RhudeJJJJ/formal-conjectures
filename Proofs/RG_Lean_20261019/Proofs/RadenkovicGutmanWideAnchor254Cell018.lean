/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor254Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor254Cell018
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (872389/8796093022208)
  b := (523433/4398046511104)
  s := [(68719476735/68719476736),(-7/1099511627776)]
  L := [(5472627164470047967394811261/680564733841876926926749214863536422912),(121516176493/37778931862957161709568),(145818743167/453347182355485940514816),(1/18889465931478580854784),(-1/28334198897217871282176)]
  c := (303791834159/37778931862957161709568)
  R := (-255464299942517/20000000000000)
  total := (-251506907/1000000000000000)
  k := 37
  n := 32
  sFloor := (1099511627753/2199023255552)
  nFloor := (919120202887/1208925819614629174706176)
  eFloor := (828082691865/1208925819614629174706176)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=872389,width:=174477,den:=8796093022208,localDen:=2041694201525630780780247644590609268736,lowerC:=16417881493400063016978874368,s:=[2041694201495920219837398517993030287360,-12998370412496492886440804352],L:=[16417881493410143902184433783,6567122486080346705243406336,656709237390535259777400832,108086391056891904,-72057594037927936],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor254Source.source.poly i) 872389 174477 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor254Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 31) (CoreQuotient.fused G u 0 31) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 31 WideAnchor254Source.data
    WideAnchor254Source.path_checked WideAnchor254Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor254Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 31 0) (CoreQuotient.fused G u 31 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 31 0 WideAnchor254Source.data
    WideAnchor254Source.path_swapped WideAnchor254Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor254Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor254Cell018
