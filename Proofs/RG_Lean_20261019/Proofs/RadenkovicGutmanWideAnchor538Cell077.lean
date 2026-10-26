/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor538Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor538Cell077
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (625051/134217728)
  b := (750061/134217728)
  s := [(43026628333/68719476736),(-650578057519/8796093022208),(27557357665/4398046511104)]
  L := [(140240120885860039801/590295810358705651712),(6112268595839/105553116266496),(-130792593557/52776558133248),(-1660829057/6597069766656),(184637969/3298534883328)]
  c := (522435161791/2199023255552)
  R := (-2874535364277/4000000000000)
  total := (-4945346539/8000000000000)
  k := 3
  n := 32
  sFloor := (306996567777/1099511627776)
  nFloor := (630422558033/562949953421312)
  eFloor := (1220222317167/1125899906842624)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=625051,width:=125010,den:=134217728,localDen:=1770887431076116955136,lowerC:=420720362657402585088,s:=[1108787769284291985408,-130978663150280245248,11096057806439055360],L:=[420720362657580119403,102546850482407604224,-4388671186611994624,-445825405253844992,99126754806857728],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor538Source.source.poly i) 625051 125010 134217728
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor538Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 16) (CoreQuotient.fused G u 5 16) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 16 WideAnchor538Source.data
    WideAnchor538Source.path_checked WideAnchor538Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor538Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 16 5) (CoreQuotient.fused G u 16 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 16 5 WideAnchor538Source.data
    WideAnchor538Source.path_swapped WideAnchor538Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor538Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor538Cell077
