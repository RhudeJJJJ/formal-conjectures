/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor027Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor027Cell125
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (241095/8192)
  b := (144657/4096)
  s := [(2813490889795/144115188075855872),(-402208931383/36028797018963968),(212928021769/72057594037927936)]
  L := [(591629994657059308911/590295810358705651712),(-5885945809/6597069766656),(36006871/137438953472),(-3281671/51539607552),(338235/34359738368)]
  c := (550622309113/549755813888)
  R := (7874524093/10000000000000)
  total := (554963934747/100000000000000)
  k := 0
  n := 32
  sFloor := (1630511207801/288230376151711744)
  nFloor := 1960225854122847689472445179470484536675784121501567802007201004428421114466432545916392823658046132089934244982791338663142160192830939955462144
  eFloor := 1955728971184651295491391649886103694855538911124991569081331350528830373816684357925161495701422565415468357846025457208651698668432646190661632
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=241095,width:=48219,den:=8192,localDen:=1770887431076116955136,lowerC:=1773678607566253326336,s:=[34572176053800960,-19769373395337216,5232919062994944],L:=[1774889983971177926733,-1579996547230203904,463945000128872448,-112757356969852928,17432499160350720],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor027Source.source.poly i) 241095 48219 8192
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor027Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 36) (CoreQuotient.fused G u 9 36) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 36 WideAnchor027Source.data
    WideAnchor027Source.path_checked WideAnchor027Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor027Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 36 9) (CoreQuotient.fused G u 36 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 36 9 WideAnchor027Source.data
    WideAnchor027Source.path_swapped WideAnchor027Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor027Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor027Cell125
