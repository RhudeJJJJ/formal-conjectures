/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor417Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor417Cell102
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (931671/2097152)
  b := (1118005/2097152)
  s := [(2496909591035/8796093022208),(-1100532893781/17592186044416),(80261088239/8796093022208)]
  L := [(234909610476552746773/295147905179352825856),(3055570611529/26388279066624),(-218157556211/13194139533312),(2518000973/1649267441664),(-50147905/824633720832)]
  c := (1750212985847/2199023255552)
  R := (-2282758003011/20000000000000)
  total := (-114317063607/15625000000000)
  k := 1
  n := 32
  sFloor := (2026904232383/17592186044416)
  nFloor := (1681560909101/34359738368)
  eFloor := (1178491113347/34359738368)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=931671,width:=186334,den:=2097152,localDen:=885443715538058477568,lowerC:=704728831429441486848,s:=[251347149247595151360,-55391634222206681088,8079345682684575744],L:=[704728831429658240319,102527936305748246528,-14640305770336354304,1351841478791397376,-53845902984478720],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor417Source.source.poly i) 931671 186334 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor417Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 4) (CoreQuotient.fused G u 2 4) (((52/27) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (52/27) 2 4 WideAnchor417Source.data
    WideAnchor417Source.path_checked WideAnchor417Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor417Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 2) (CoreQuotient.fused G u 4 2) (((52/27) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (52/27) 4 2 WideAnchor417Source.data
    WideAnchor417Source.path_swapped WideAnchor417Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor417Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor417Cell102
