/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor240Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor240Cell071
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (837315/536870912)
  b := (502389/268435456)
  s := [(2198279466179/2199023255552),(-594599025/4398046511104),(-29610081/2199023255552)]
  L := [(3520933453981211685936111/19807040628566084398385987584),(1920360759373/27021597764222976),(95817883721/13510798882111488),(-4997803/1688849860263936),(-123857/844424930131968)]
  c := (1601135160845/9007199254740992)
  R := (-215876665013337/50000000000000)
  total := (-658761297359/500000000000000)
  k := 13
  n := 32
  sFloor := (2197952556585/4398046511104)
  nFloor := (578012396111/4503599627370496)
  eFloor := (1099999601539/9007199254740992)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=837315,width:=167463,den:=536870912,localDen:=59421121885698253195157962752,lowerC:=10562800361940441177784320,s:=[59401023508439743586006728704,-8033507842274580706099200,-800111698548061221421056],L:=[10562800361943635057808333,4222917968910725358288896,421411509200512807337984,-175844560378680836096,-8715661547612930048],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor240Source.source.poly i) 837315 167463 536870912
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor240Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 22) (CoreQuotient.fused G u 0 22) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 22 WideAnchor240Source.data
    WideAnchor240Source.path_checked WideAnchor240Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor240Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 22 0) (CoreQuotient.fused G u 22 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 22 0 WideAnchor240Source.data
    WideAnchor240Source.path_swapped WideAnchor240Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor240Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor240Cell071
