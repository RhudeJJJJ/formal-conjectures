/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor256Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor256Cell026
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (937775/2199023255552)
  b := (562665/1099511627776)
  s := [(1099511627507/1099511627776),(-431/4398046511104),(-21/2199023255552)]
  L := [(1443240819243307237995890741/10633823966279326983230456482242756608),(2050968559231/37778931862957161709568),(307645283305/56668397794435742564352),(-3/2361183241434822606848),(-1/3541774862152233910272)]
  c := (640927675041/4722366482869645213696)
  R := (-284005181803303/25000000000000)
  total := (-120114901/125000000000000)
  k := 33
  n := 32
  sFloor := (2199023254777/4398046511104)
  nFloor := (1122058701585/75557863725914323419136)
  eFloor := (1010983647929/75557863725914323419136)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=937775,width:=187555,den:=2199023255552,localDen:=31901471898837980949691369446728269824,lowerC:=4329722457729128924398485504,s:=[31901471891033155858259323494825197568,-3126282169523431045790171136,-304649306542886552025956352],L:=[4329722457729921713987672223,1731888982331500247654596608,173188897906836084264796160,-40532396646334464,-9007199254740992],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor256Source.source.poly i) 937775 187555 2199023255552
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor256Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 33) (CoreQuotient.fused G u 0 33) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 33 WideAnchor256Source.data
    WideAnchor256Source.path_checked WideAnchor256Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor256Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 33 0) (CoreQuotient.fused G u 33 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 33 0 WideAnchor256Source.data
    WideAnchor256Source.path_swapped WideAnchor256Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor256Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor256Cell026
