/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor509Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor509Cell070
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1395525/1073741824)
  b := (837315/536870912)
  s := [(274382279701/274877906944),(-789683225/1099511627776),(-77140025/1099511627776)]
  L := [(18334019555956850251191/19342813113834066795298816),(5104637645689/13510798882111488),(251679383995/6755399441055744),(-88211857/844424930131968),(-2098651/422212465065984)]
  c := (533590196747/562949953421312)
  R := (-43508236799823/12500000000000)
  total := (-176096416177/200000000000000)
  k := 11
  n := 32
  sFloor := (548331147777/1099511627776)
  nFloor := (1490107612847/9007199254740992)
  eFloor := (709294566897/4503599627370496)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1395525,width:=279105,den:=1073741824,localDen:=58028439341502200385896448,lowerC:=55002058667869694066688,s:=[57923809341491756654395392,-41676762631063260364800,-4071185013812704051200],L:=[55002058667870550753573,21924251746164690386944,2161909446671901655040,-6061872654950858752,-288436397142966272],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor509Source.source.poly i) 1395525 279105 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor509Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 39) (CoreQuotient.fused G u 4 39) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 39 WideAnchor509Source.data
    WideAnchor509Source.path_checked WideAnchor509Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor509Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 39 4) (CoreQuotient.fused G u 39 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 39 4 WideAnchor509Source.data
    WideAnchor509Source.path_swapped WideAnchor509Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor509Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor509Cell070
