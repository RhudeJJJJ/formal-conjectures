/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor516Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor516Cell007
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (939307/70368744177664)
  b := (4403/274877906944)
  s := [(4398046511103/4398046511104)]
  L := [(674217813693/309485009821345068724781056),(3236238615005/3713820117856140824697372672),(161811586247/1856910058928070412348686336),(-5/232113757366008801543585792),(1/116056878683004400771792896)]
  c := (674217813693/309485009821345068724781056)
  R := (-1688006641395333/100000000000000)
  total := (-5601737/125000000000000)
  k := 49
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (1255624052189/309485009821345068724781056)
  eFloor := (1232045046087/309485009821345068724781056)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=939307,width:=187861,den:=70368744177664,localDen:=3713820117856140824697372672,lowerC:=8090613764316,s:=[3713820117855296399767240704],L:=[8090613764316,3236238615005,323623172494,-80,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor516Source.source.poly i) 939307 187861 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor516Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((25/13) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (25/13) 4 4 WideAnchor516Source.data
    WideAnchor516Source.path_checked WideAnchor516Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor516Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((25/13) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (25/13) 4 4 WideAnchor516Source.data
    WideAnchor516Source.path_swapped WideAnchor516Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor516Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor516Cell007
