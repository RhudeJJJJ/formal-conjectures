/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor019Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor019Cell042
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1083619/137438953472)
  b := (650171/68719476736)
  s := [(1099510345437/1099511627776),(-2051731/4398046511104),(-102585/2199023255552)]
  L := [(1577788163977716746804223/2535301200456458802993406410752),(3443958955403/13835058055282163712),(172196457371/6917529027641081856),(-21347/864691128455135232),(-539/432345564227567616)]
  c := (1434989975657/2305843009213693952)
  R := (-714489951732291/100000000000000)
  total := (-11118755913/1000000000000000)
  k := 21
  n := 32
  sFloor := (2199019562423/4398046511104)
  nFloor := (1594503864231/295147905179352825856)
  eFloor := (373525019907/73786976294838206464)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1083619,width:=216723,den:=137438953472,localDen:=7605903601369376408980219232256,lowerC:=4733364491930612055146496,s:=[7605894730752120632742953091072,-3548227187352766129373184,-354817357650280191098880],L:=[4733364491933150240412669,1893336458524442560036864,189332007141248803536896,-187770197745074176,-9482188277940224],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor019Source.source.poly i) 1083619 216723 137438953472
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor019Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 28) (CoreQuotient.fused G u 9 28) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 28 WideAnchor019Source.data
    WideAnchor019Source.path_checked WideAnchor019Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor019Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 28 9) (CoreQuotient.fused G u 28 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 28 9 WideAnchor019Source.data
    WideAnchor019Source.path_swapped WideAnchor019Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor019Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor019Cell042
