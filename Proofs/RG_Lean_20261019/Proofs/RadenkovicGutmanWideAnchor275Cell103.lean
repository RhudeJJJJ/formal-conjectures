/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor275Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor275Cell103
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1118005/2097152)
  b := (670803/1048576)
  s := [(4981375135237/17592186044416),(-544693467111/8796093022208),(36962668091/4398046511104)]
  L := [(64881741653180446975/73786976294838206464),(820448685281/6597069766656),(-20610150375/1099511627776),(643448611/412316860416),(-3558029/68719476736)]
  c := (1933626581823/2199023255552)
  R := (-3215399734849/50000000000000)
  total := (-3576501727257/1000000000000000)
  k := 1
  n := 32
  sFloor := (2019919436689/17592186044416)
  nFloor := (1786658966703/34359738368)
  eFloor := (567560004601/17179869184)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1118005,width:=223601,den:=2097152,localDen:=221360928884514619392,lowerC:=194645224959516868608,s:=[62680204965675270144,-13707659927265214464,1860391999497043968],L:=[194645224959541340925,27529689619750715392,-4149371335606272000,345448842612703232,-11461213644914688],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor275Source.source.poly i) 1118005 223601 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor275Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 4) (CoreQuotient.fused G u 0 4) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 0 4 WideAnchor275Source.data
    WideAnchor275Source.path_checked WideAnchor275Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor275Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 0) (CoreQuotient.fused G u 4 0) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 4 0 WideAnchor275Source.data
    WideAnchor275Source.path_swapped WideAnchor275Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor275Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor275Cell103
