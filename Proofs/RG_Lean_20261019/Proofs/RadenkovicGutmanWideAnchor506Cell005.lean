/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor506Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor506Cell005
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (652297/70368744177664)
  b := (195689/17592186044416)
  s := [(4398046511103/4398046511104)]
  L := [(14466744970989260799487043913/696898287454081973172991196020261297061888),(7709406774167/928455029464035206174343168),(385469156729/464227514732017603087171584),(19/58028439341502200385896448),(-5/29014219670751100192948224)]
  c := (1606131335817/77371252455336267181195264)
  R := (-1575290401091427/100000000000000)
  total := (-2903107/100000000000000)
  k := 46
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (1624429327009/309485009821345068724781056)
  eFloor := (1135072137291/154742504910672534362390528)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=652297,width:=130459,den:=70368744177664,localDen:=2090694862362245919518973588060783891185664,lowerC:=43400234912961109053923131392,s:=[2090694862361770550543888002035222627483648],L:=[43400234912967782398461131739,17360040737693039403955388416,1735998750607543720774467584,684547143360315392,-360287970189639680],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor506Source.source.poly i) 652297 130459 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor506Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 36) (CoreQuotient.fused G u 4 36) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 36 WideAnchor506Source.data
    WideAnchor506Source.path_checked WideAnchor506Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor506Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 36 4) (CoreQuotient.fused G u 36 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 36 4 WideAnchor506Source.data
    WideAnchor506Source.path_swapped WideAnchor506Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor506Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor506Cell005
