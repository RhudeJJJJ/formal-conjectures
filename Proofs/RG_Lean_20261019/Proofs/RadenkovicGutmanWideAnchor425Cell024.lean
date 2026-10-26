/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor425Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor425Cell024
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (651233/2199023255552)
  b := (1562959/4398046511104)
  s := [(4398046511093/4398046511104),(-1/1099511627776)]
  L := [(656240171957527877498543505/680564733841876926926749214863536422912),(5595435949133/14507109835375550096474112),(279771582715/7253554917687775048237056),(-17/906694364710971881029632),(5/453347182355485940514816)]
  c := (1165716717745/1208925819614629174706176)
  R := (-276674172226477/20000000000000)
  total := (-406904249/500000000000000)
  k := 40
  n := 32
  sFloor := (274877906943/549755813888)
  nFloor := (488552645627/302231454903657293676544)
  eFloor := (290156029801/151115727451828646838272)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1302466,width:=260493,den:=4398046511104,localDen:=2041694201525630780780247644590609268736,lowerC:=1968720515870977373314744320,s:=[2041694201520524278118195450956650381312,-1856910058928070412348686336],L:=[1968720515872583632495630515,787487601734089262837530624,78748699729007993725911040,-38280596832649216,22517998136852480],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor425Source.source.poly i) 1302466 260493 4398046511104
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor425Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 2 6 WideAnchor425Source.data
    WideAnchor425Source.path_checked WideAnchor425Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor425Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 6 2 WideAnchor425Source.data
    WideAnchor425Source.path_swapped WideAnchor425Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor425Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor425Cell024
