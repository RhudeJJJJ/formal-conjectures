/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor247Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor247Cell096
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (624031/4194304)
  b := (748837/4194304)
  s := [(1820814523323/2199023255552),(-120546904649/2199023255552),(-415964409/1099511627776)]
  L := [(941393486213579689305/4722366482869645213696),(894823761019/13194139533312),(12342363723/4398046511104),(-55632929/103079215104),(6202229/274877906944)]
  c := (1753482010613/8796093022208)
  R := (-16127041167351/20000000000000)
  total := (-5415871551153/250000000000000)
  k := 3
  n := 32
  sFloor := (13276841327/34359738368)
  nFloor := (1353886761433/2199023255552)
  eFloor := (1277979392823/4398046511104)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=624031,width:=124806,den:=4194304,localDen:=14167099448608935641088,lowerC:=2824180458640184967168,s:=[11730508244631171366912,-776617519652228038656,-5359660598864904192],L:=[2824180458640739067915,960809697315081158656,39757536409216352256,-7646131540342079488,319660448607633408],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor247Source.source.poly i) 624031 124806 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor247Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 2 WideAnchor247Source.data
    WideAnchor247Source.path_checked WideAnchor247Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor247Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 2 0 WideAnchor247Source.data
    WideAnchor247Source.path_swapped WideAnchor247Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor247Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor247Cell096
