/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor007Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor007Cell015
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (504855/8796093022208)
  b := (302913/4398046511104)
  s := [(4398046510905/4398046511104),(-77/4398046511104),(-5/2199023255552)]
  L := [(3557826955341/151115727451828646838272),(1067348086555/113336795588871485128704),(106734808609/113336795588871485128704),(1/3541774862152233910272),(-1/7083549724304467820544)]
  c := (889456738835/37778931862957161709568)
  R := (-76475505732813/6250000000000)
  total := (-139382913/1000000000000000)
  k := 36
  n := 32
  sFloor := (2199023255409/4398046511104)
  nFloor := (962565279893/4835703278458516698824704)
  eFloor := (920541560133/4835703278458516698824704)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=504855,width:=100971,den:=8796093022208,localDen:=453347182355485940514816,lowerC:=10673480866020,s:=[453347182334973176709120,-7937099563008,-1030792151040],L:=[10673480866023,4269392346220,426939234436,128,-64],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor007Source.source.poly i) 504855 100971 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor007Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 16) (CoreQuotient.fused G u 9 16) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 16 WideAnchor007Source.data
    WideAnchor007Source.path_checked WideAnchor007Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor007Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 16 9) (CoreQuotient.fused G u 16 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 16 9 WideAnchor007Source.data
    WideAnchor007Source.path_swapped WideAnchor007Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor007Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor007Cell015
