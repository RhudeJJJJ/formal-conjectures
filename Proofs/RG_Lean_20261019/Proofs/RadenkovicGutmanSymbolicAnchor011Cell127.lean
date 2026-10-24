/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor011Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor011Cell127
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (90327/134217728)
  b := (1589755/2147483648)
  s := [(4368789851383/4398046511104),(-5790508511/4398046511104),(-137762705/2199023255552)]
  L := [(542065231766001366697387/154742504910672534362390528),(391568562481/562949953421312),(445694485/13194139533312),(-6905959/70368744177664),(-116491/52776558133248)]
  c := (1972021825225/562949953421312)
  R := (-282706570391563/100000000000000)
  total := (-46756329973/250000000000000)
  k := 9
  n := 32
  sFloor := (2181361908731/4398046511104)
  nFloor := (281326988539/9007199254740992)
  eFloor := (1072040763223/36028797018963968)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1445232,width:=144523,den:=2147483648,localDen:=464227514732017603087171584,lowerC:=1626195695297203745587200,s:=[461139383126917579662163968,-611206218103717632147456,-29082565636103979663360],L:=[1626195695298004100092161,322900640639544503304192,15681480598180352491520,-45559093328665903104,-1024665672250032128],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor011Source.source.poly i) 1445232 144523 2147483648
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor011Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 20) (CoreQuotient.fused G u 9 20) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 20 SymbolicAnchor011Source.data
    SymbolicAnchor011Source.path_checked SymbolicAnchor011Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor011Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 20 9) (CoreQuotient.fused G u 20 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 20 9 SymbolicAnchor011Source.data
    SymbolicAnchor011Source.path_swapped SymbolicAnchor011Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor011Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor011Cell127
