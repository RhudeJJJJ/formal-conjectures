/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor419Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor419Cell082
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (388831/33554432)
  b := (466597/33554432)
  s := [(4387277917323/4398046511104),(-1073864863/1099511627776),(-52867209/549755813888)]
  L := [(6035174992910682343273701/4951760157141521099596496896),(6581340626405/13510798882111488),(327987889105/6755399441055744),(-26933915/844424930131968),(-669133/422212465065984)]
  c := (1372239920081/1125899906842624)
  R := (-67098935291891/20000000000000)
  total := (-377920746951/50000000000000)
  k := 10
  n := 32
  sFloor := (2191279760099/4398046511104)
  nFloor := (1363432924241/562949953421312)
  eFloor := (685606152125/281474976710656)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=388831,width:=77766,den:=33554432,localDen:=14855280471424563298789490688,lowerC:=18105524978729621517238272,s:=[14818907395220001418333126656,-14508772190559206211846144,-1428556456515108794793984],L:=[18105524978732047029821103,7236260545086881037025280,721252995681305451560960,-473826443584486768640,-23543024448916422656],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor419Source.source.poly i) 388831 77766 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor419Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 4) (CoreQuotient.fused G u 2 4) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 2 4 WideAnchor419Source.data
    WideAnchor419Source.path_checked WideAnchor419Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor419Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 2) (CoreQuotient.fused G u 4 2) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 4 2 WideAnchor419Source.data
    WideAnchor419Source.path_swapped WideAnchor419Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor419Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor419Cell082
