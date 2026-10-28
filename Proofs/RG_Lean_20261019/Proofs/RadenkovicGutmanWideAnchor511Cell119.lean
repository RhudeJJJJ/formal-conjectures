/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor511Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor511Cell119
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1291879/131072)
  b := (775127/65536)
  s := [(564316020411/1125899906842624),(-5052337377905/18014398509481984),(656633773787/9007199254740992)]
  L := [(75175506267463904829/73786976294838206464),(-92916304669/13194139533312),(4255699597/2199023255552),(-361149263/824633720832),(8783779/137438953472)]
  c := (1114175899011/1099511627776)
  R := (331223028619/50000000000000)
  total := (619756302339/40000000000000)
  k := 0
  n := 32
  sFloor := (1322496624061/9007199254740992)
  nFloor := 130627755326496539171719420567782375055153738661482958754220907082803873453687845945492194625323008
  eFloor := 128086526373044099931379670925107392818310903592811653877669083593363069426934839030845084916514816
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1291879,width:=258375,den:=131072,localDen:=221360928884514619392,lowerC:=224313236636420800512,s:=[110949044140965888,-62083121699696640,16137431624589312],L:=[225526518802391714487,-1558876913353621504,428392748219891712,-96945267097468928,14147266327609344],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor511Source.source.poly i) 1291879 258375 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor511Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 41) (CoreQuotient.fused G u 4 41) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 41 WideAnchor511Source.data
    WideAnchor511Source.path_checked WideAnchor511Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor511Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 41 4) (CoreQuotient.fused G u 41 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 41 4 WideAnchor511Source.data
    WideAnchor511Source.path_swapped WideAnchor511Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor511Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor511Cell119
