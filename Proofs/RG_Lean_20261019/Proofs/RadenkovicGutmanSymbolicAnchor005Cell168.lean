/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor005Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor005Cell168
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1124219/33554432)
  b := (38645/1048576)
  s := [(2546156302271/8796093022208),(-120611924485/17592186044416),(10610754435/8796093022208)]
  L := [(1374836299728441615463/2361183241434822606848),(264102724937/26388279066624),(-22249971745/13194139533312),(281742163/1649267441664),(-9533327/824633720832)]
  c := (1280416082337/2199023255552)
  R := (-13520704939847/50000000000000)
  total := (-893165027439/1000000000000000)
  k := 1
  n := 32
  sFloor := (1248230547231/8796093022208)
  nFloor := (640054853037/8796093022208)
  eFloor := (302860286819/4398046511104)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1124219,width:=112421,den:=33554432,localDen:=7083549724304467820544,lowerC:=4124508899182393688064,s:=[2050435884142169161728,-48564775422252810240,8544908115789742080],L:=[4124508899185324846389,70894535399306166272,-11945362622712381440,1210073375989301248,-81890655374147584],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor005Source.source.poly i) 1124219 112421 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor005Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 14) (CoreQuotient.fused G u 9 14) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 14 SymbolicAnchor005Source.data
    SymbolicAnchor005Source.path_checked SymbolicAnchor005Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor005Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 9) (CoreQuotient.fused G u 14 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 14 9 SymbolicAnchor005Source.data
    SymbolicAnchor005Source.path_swapped SymbolicAnchor005Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor005Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor005Cell168
