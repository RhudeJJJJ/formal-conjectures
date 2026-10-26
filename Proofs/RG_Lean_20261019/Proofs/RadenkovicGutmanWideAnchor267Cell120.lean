/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor267Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor267Cell120
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (775127/65536)
  b := (116269/8192)
  s := [(2663505473515/9007199254740992),(-3015309377787/18014398509481984),(395692504345/9007199254740992)]
  L := [(149556065218850328545/147573952589676412928),(-1415432369/274877906944),(2408529683/1649267441664),(-11763857/34359738368),(5305453/103079215104)]
  c := (1109903622725/1099511627776)
  R := (470353935573/100000000000000)
  total := (13252083245099/1000000000000000)
  k := 0
  n := 32
  sFloor := (775771644483/9007199254740992)
  nFloor := 276447448710664190620223553550149698344072473025078364648621506313109046190231961571986577451135270912
  eFloor := 272622313371728215474675216604251840620201577669143940570923178749205727725808962635844554957141311488
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=775127,width:=155025,den:=65536,localDen:=442721857769029238784,lowerC:=446906227623356006400,s:=[130916621034209280,-74104243268493312,19449077973565440],L:=[448668195656550985635,-2279713400458051584,646534763745640448,-151576143269462016,22786747125465088],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor267Source.source.poly i) 775127 155025 65536
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor267Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 43) (CoreQuotient.fused G u 0 43) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 43 WideAnchor267Source.data
    WideAnchor267Source.path_checked WideAnchor267Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor267Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 43 0) (CoreQuotient.fused G u 43 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 43 0 WideAnchor267Source.data
    WideAnchor267Source.path_swapped WideAnchor267Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor267Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor267Cell120
