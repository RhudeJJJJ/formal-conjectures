/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor024Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor024Cell127
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (90327/134217728)
  b := (1589755/2147483648)
  s := [(2132204383897/2199023255552),(-12754458261/2199023255552),(-7887975/34359738368)]
  L := [(55403028709435335496009/2417851639229258349412352),(1249568284553/281474976710656),(27356171965/140737488355328),(-44875823/17592186044416),(-316921/8796093022208)]
  c := (403110088587/17592186044416)
  R := (-94400010259423/50000000000000)
  total := (-61955426463/500000000000000)
  k := 6
  n := 32
  sFloor := (529736273809/1099511627776)
  nFloor := (541193736805/9007199254740992)
  eFloor := (1457461269841/36028797018963968)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1445232,width:=144523,den:=2147483648,localDen:=2417851639229258349412352,lowerC:=55403028709402491224064,s:=[2344383512889713672323072,-14023675163953160257536,-555066894854809190400],L:=[55403028709435335496009,10733709832547913957376,469975455733708226560,-6167686149314707456,-87114581146599424],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor024Source.source.poly i) 1445232 144523 2147483648
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor024Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 33) (CoreQuotient.fused G u 9 33) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 33 SymbolicAnchor024Source.data
    SymbolicAnchor024Source.path_checked SymbolicAnchor024Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor024Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 33 9) (CoreQuotient.fused G u 33 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 33 9 SymbolicAnchor024Source.data
    SymbolicAnchor024Source.path_swapped SymbolicAnchor024Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor024Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor024Cell127
