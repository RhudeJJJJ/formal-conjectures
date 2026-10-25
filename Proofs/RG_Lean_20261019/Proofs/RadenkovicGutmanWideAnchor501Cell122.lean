/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor501Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor501Cell122
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (558091/32768)
  b := (669709/32768)
  s := [(7191620045807/72057594037927936),(-4089624621987/72057594037927936),(538751662571/36028797018963968)]
  L := [(594196432431400874503/590295810358705651712),(-33896488981/13194139533312),(1629086513/2199023255552),(-145723121/824633720832),(3700755/137438953472)]
  c := (1104602246945/1099511627776)
  R := (230960309217/100000000000000)
  total := (9394823829547/1000000000000000)
  k := 0
  n := 32
  sFloor := (2089749374481/72057594037927936)
  nFloor := 2851342094050633348723362413906669460822930651985302043256044162253846904201101896052252491120640
  eFloor := 2832058945669138878195993194734033458105006627876874721025156938872368620625324424781672438824960
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=558091,width:=111618,den:=32768,localDen:=1770887431076116955136,lowerC:=1779086447143834091520,s:=[176741254245752832,-100506614709952512,26480721718689792],L:=[1782589297294202623509,-4549509738206855168,1311913742941814784,-312938019483025408,47683865086525440],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor501Source.source.poly i) 558091 111618 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor501Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 31) (CoreQuotient.fused G u 4 31) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 31 WideAnchor501Source.data
    WideAnchor501Source.path_checked WideAnchor501Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor501Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 31 4) (CoreQuotient.fused G u 31 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 31 4 WideAnchor501Source.data
    WideAnchor501Source.path_swapped WideAnchor501Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor501Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor501Cell122
