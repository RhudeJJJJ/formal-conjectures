/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor245Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor245Cell125
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (241095/8192)
  b := (144657/4096)
  s := [(1408363958981/72057594037927936),(-1611799816641/144115188075855872),(213443617711/72057594037927936)]
  L := [(591631531979313514229/590295810358705651712),(-11799152521/13194139533312),(1734977087/6597069766656),(-52796963/824633720832),(4086841/412316860416)]
  c := (1101246005603/1099511627776)
  R := (4925514513/6250000000000)
  total := (1111004558009/200000000000000)
  k := 0
  n := 32
  sFloor := (1631815336743/288230376151711744)
  nFloor := 24976827430130336645568375297870800352218979833017152947132529172618547962563277751773560832
  eFloor := 24919463120437728723876354203262165815769661232869219908890442276527585501672957125234524160
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=241095,width:=48219,den:=8192,localDen:=1770887431076116955136,lowerC:=1773680842093319159808,s:=[34611952655917056,-19805796146884608,5245590348865536],L:=[1774894595937940542687,-1583655443694092288,465729365498396672,-113380614706561024,17552848438951936],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor245Source.source.poly i) 241095 48219 8192
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor245Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 27) (CoreQuotient.fused G u 0 27) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 27 WideAnchor245Source.data
    WideAnchor245Source.path_checked WideAnchor245Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor245Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 27 0) (CoreQuotient.fused G u 27 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 27 0 WideAnchor245Source.data
    WideAnchor245Source.path_swapped WideAnchor245Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor245Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor245Cell125
