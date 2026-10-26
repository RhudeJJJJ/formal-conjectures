/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor428Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor428Cell007
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (939307/70368744177664)
  b := (4403/274877906944)
  s := [(4398046511103/4398046511104)]
  L := [(2128119318494758825521221353/1393796574908163946345982392040522594123776),(1134087377209/1856910058928070412348686336),(18901416039/309485009821345068724781056),(1/232113757366008801543585792)]
  c := (1890149653233/1237940039285380274899124224)
  R := (-852889228173123/50000000000000)
  total := (-5661043/125000000000000)
  k := 50
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (339755264773/154742504910672534362390528)
  eFloor := (1184158652401/309485009821345068724781056)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=939307,width:=187861,den:=70368744177664,localDen:=4181389724724491839037947176121567782371328,lowerC:=6384357955480958272511410176,s:=[4181389724723541101087776004070445254967296],L:=[6384357955484276476563664059,2553737744702017768974712832,255373230690045349469356032,18014398509481984],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor428Source.source.poly i) 939307 187861 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor428Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 2 6 WideAnchor428Source.data
    WideAnchor428Source.path_checked WideAnchor428Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor428Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 6 2 WideAnchor428Source.data
    WideAnchor428Source.path_swapped WideAnchor428Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor428Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor428Cell007
