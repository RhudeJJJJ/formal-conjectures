/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor028Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor028Cell022
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (904491/4398046511104)
  b := (1085389/4398046511104)
  s := [(4398046495479/4398046511104),(-6253/4398046511104),(-311/2199023255552)]
  L := [(3109300097817/1180591620717411303424),(3731155978577/3541774862152233910272),(186557589949/1770887431076116955136),(-71/221360928884514619392),(-1/110680464442257309696)]
  c := (388662512227/147573952589676412928)
  R := (-493872096783439/50000000000000)
  total := (-80483619/200000000000000)
  k := 29
  n := 32
  sFloor := (1099511622151/2199023255552)
  nFloor := (921010382909/151115727451828646838272)
  eFloor := (1242395675163/302231454903657293676544)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=904491,width:=180898,den:=4398046511104,localDen:=3541774862152233910272,lowerC:=9327900293448,s:=[3541774849569321910272,-5035580719104,-500900560896],L:=[9327900293451,3731155978577,373115179898,-1136,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor028Source.source.poly i) 904491 180898 4398046511104
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor028Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 37) (CoreQuotient.fused G u 9 37) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 37 WideAnchor028Source.data
    WideAnchor028Source.path_checked WideAnchor028Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor028Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 37 9) (CoreQuotient.fused G u 37 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 37 9 WideAnchor028Source.data
    WideAnchor028Source.path_swapped WideAnchor028Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor028Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor028Cell022
