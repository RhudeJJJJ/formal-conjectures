/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor037Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor037Cell071
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (837315/536870912)
  b := (502389/268435456)
  s := [(4396806926335/4398046511104),(-123909353/1099511627776),(-12363685/1099511627776)]
  L := [(28193155367617169150862215/316912650057057350374175801344),(7692290367019/216172782113783808),(384581007563/108086391056891904),(-840415/13510798882111488),(-21491/6755399441055744)]
  c := (1602595339569/18014398509481984)
  R := (-93273022319947/20000000000000)
  total := (-1425468682951/1000000000000000)
  k := 14
  n := 32
  sFloor := (2198130917091/4398046511104)
  nFloor := (400980485083/4503599627370496)
  eFloor := (1270564590435/9007199254740992)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=837315,width:=167463,den:=536870912,localDen:=950737950171172051122527404032,lowerC:=84579466102835647308890112,s:=[950469985682991449089171783680,-107143318271715696124624896,-10690768734513828640849920],L:=[84579466102851507452586645,33831050811066820618878976,3382810317098626374959104,-59138948138071490560,-3024589362244354048],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor037Source.source.poly i) 837315 167463 536870912
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor037Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 16) (CoreQuotient.fused G u 10 16) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 16 WideAnchor037Source.data
    WideAnchor037Source.path_checked WideAnchor037Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor037Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 16 10) (CoreQuotient.fused G u 16 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 16 10 WideAnchor037Source.data
    WideAnchor037Source.path_swapped WideAnchor037Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor037Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor037Cell071
