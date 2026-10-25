/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor377Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor377Cell073
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1205733/536870912)
  b := (1446879/536870912)
  s := [(4394826010379/4398046511104),(-1285988193/4398046511104),(-63688297/2199023255552)]
  L := [(1073111944099225966637787/4951760157141521099596496896),(4679576355881/54043195528445952),(77649177757/9007199254740992),(-25688177/3377699720527872),(-209341/562949953421312)]
  c := (975989627567/4503599627370496)
  R := (-105461694916337/25000000000000)
  total := (-1852757247677/1000000000000000)
  k := 13
  n := 32
  sFloor := (549176580699/1099511627776)
  nFloor := (62652935959/562949953421312)
  eFloor := (847107663729/4503599627370496)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1205733,width:=241146,den:=536870912,localDen:=14855280471424563298789490688,lowerC:=3219335832296052517502976,s:=[14844402587025770989630783488,-4343681960098243119415296,-430239885955592217427968],L:=[3219335832297677899913361,1286312154089200145137664,128064260746600563867648,-112977797231472017408,-5524148728086134784],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor377Source.source.poly i) 1205733 241146 536870912
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor377Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 14) (CoreQuotient.fused G u 2 14) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 2 14 WideAnchor377Source.data
    WideAnchor377Source.path_checked WideAnchor377Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor377Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 2) (CoreQuotient.fused G u 14 2) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 14 2 WideAnchor377Source.data
    WideAnchor377Source.path_swapped WideAnchor377Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor377Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor377Cell073
