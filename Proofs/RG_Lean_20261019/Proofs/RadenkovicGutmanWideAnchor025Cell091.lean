/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor025Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor025Cell091
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (501569/8388608)
  b := (1203765/16777216)
  s := [(2002177049193/8796093022208),(17743897709/2199023255552),(2378374645/4398046511104)]
  L := [(213024603539020564581/295147905179352825856),(-44266117361/8796093022208),(-12125636345/4398046511104),(462811439/549755813888),(-29592363/274877906944)]
  c := (785821068567/1099511627776)
  R := (-8397306676789/50000000000000)
  total := (-123537098857/62500000000000)
  k := 1
  n := 32
  sFloor := (2002177049193/17592186044416)
  nFloor := (1228496978943/1099511627776)
  eFloor := (1070902623199/1099511627776)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1003138,width:=200627,den:=16777216,localDen:=295147905179352825856,lowerC:=210942236875189911552,s:=[67181913649107173376,2381545636366385152,159610020592353280],L:=[213024603539020564581,-1485324424893693952,-813737680390062080,248469999339962368,-31774557824090112],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor025Source.source.poly i) 1003138 200627 16777216
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor025Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 34) (CoreQuotient.fused G u 9 34) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 34 WideAnchor025Source.data
    WideAnchor025Source.path_checked WideAnchor025Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor025Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 34 9) (CoreQuotient.fused G u 34 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 34 9 WideAnchor025Source.data
    WideAnchor025Source.path_swapped WideAnchor025Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor025Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor025Cell091
