/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor257Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor257Cell125
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (241095/8192)
  b := (144657/4096)
  s := [(1408363958981/72057594037927936),(-1611799816641/144115188075855872),(213443617711/72057594037927936)]
  L := [(591631532020960333319/590295810358705651712),(-11799152521/13194139533312),(1734977087/6597069766656),(-52796963/824633720832),(4086841/412316860416)]
  c := (68827875355/68719476736)
  R := (9851029463/12500000000000)
  total := (555502299729/100000000000000)
  k := 0
  n := 32
  sFloor := (1631815336743/288230376151711744)
  nFloor := 9283796278466047024486413678941993798451867195205799455253029106139950147203744258457886211525161509467866529792
  eFloor := 9262474172355445754627937193939690852760108704432835023743638141320928476184279701683381620702269274954523475968
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=241095,width:=48219,den:=8192,localDen:=1770887431076116955136,lowerC:=1773680842217336340480,s:=[34611952655917056,-19805796146884608,5245590348865536],L:=[1774894596062880999957,-1583655443694092288,465729365498396672,-113380614706561024,17552848438951936],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor257Source.source.poly i) 241095 48219 8192
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor257Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 34) (CoreQuotient.fused G u 0 34) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 34 WideAnchor257Source.data
    WideAnchor257Source.path_checked WideAnchor257Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor257Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 34 0) (CoreQuotient.fused G u 34 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 34 0 WideAnchor257Source.data
    WideAnchor257Source.path_swapped WideAnchor257Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor257Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor257Cell125
