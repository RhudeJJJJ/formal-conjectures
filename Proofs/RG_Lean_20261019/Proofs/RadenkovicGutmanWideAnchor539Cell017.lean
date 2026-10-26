/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor539Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor539Cell017
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (726991/8796093022208)
  b := (872389/8796093022208)
  s := [(4398046508331/4398046511104),(-277/1099511627776),(-7/274877906944)]
  L := [(1938824040781/4722366482869645213696),(4653171294317/28334198897217871282176),(232658244061/14167099448608935641088),(-11/1770887431076116955136),(-1/885443715538058477568)]
  c := (1938824040781/4722366482869645213696)
  R := (-270168678245627/25000000000000)
  total := (-22135551/125000000000000)
  k := 32
  n := 32
  sFloor := (2199023253555/4398046511104)
  nFloor := (2159685625917/4835703278458516698824704)
  eFloor := (828995186765/2417851639229258349412352)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=726991,width:=145398,den:=8796093022208,localDen:=28334198897217871282176,lowerC:=11632944244686,s:=[28334198879352954814464,-7138235645952,-721554505728],L:=[11632944244686,4653171294317,465316488122,-176,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor539Source.source.poly i) 726991 145398 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor539Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 17) (CoreQuotient.fused G u 5 17) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 17 WideAnchor539Source.data
    WideAnchor539Source.path_checked WideAnchor539Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor539Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 17 5) (CoreQuotient.fused G u 17 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 17 5 WideAnchor539Source.data
    WideAnchor539Source.path_swapped WideAnchor539Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor539Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor539Cell017
