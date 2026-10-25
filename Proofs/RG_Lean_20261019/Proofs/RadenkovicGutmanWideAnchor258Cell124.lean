/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor258Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor258Cell124
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1607301/65536)
  b := (241095/8192)
  s := [(2429866255249/72057594037927936),(-694563144121/36028797018963968),(183811995987/36028797018963968)]
  L := [(592209980674642773031/590295810358705651712),(-2809208489/2199023255552),(1205795/3221225472),(-3119887/34359738368),(1445087/103079215104)]
  c := (1101999599489/1099511627776)
  R := (14126505133/12500000000000)
  total := (6634527092901/1000000000000000)
  k := 0
  n := 32
  sFloor := (1408363958981/144115188075855872)
  nFloor := 5589036436996575506530172563250606657408300724949232849943153684893374474629823279659054426836760176371957760
  eFloor := 5570595504839129063445819820519949145686730872178772841652994435317433424080320871472873442662314754604793856
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1607301,width:=321459,den:=65536,localDen:=1770887431076116955136,lowerC:=1774894590003882491904,s:=[59716393088999424,-34139167659835392,9034727226753024],L:=[1776629942023928319093,-2262273485231357952,662892811607080960,-160797751586586624,24826405619499008],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor258Source.source.poly i) 1607301 321459 65536
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor258Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 35) (CoreQuotient.fused G u 0 35) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 35 WideAnchor258Source.data
    WideAnchor258Source.path_checked WideAnchor258Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor258Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 35 0) (CoreQuotient.fused G u 35 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 35 0 WideAnchor258Source.data
    WideAnchor258Source.path_swapped WideAnchor258Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor258Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor258Cell124
