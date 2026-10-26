/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor479Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor479Cell127
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1388707/32768)
  b := (104153/2048)
  s := [(3777860080895/576460752303423488),(-4326718328849/1152921504606846976),(573317722505/576460752303423488)]
  L := [(2363775857265734940431/2361183241434822606848),(-5746310711/13194139533312),(282755739/2199023255552),(-25909843/824633720832),(670313/137438953472)]
  c := (1100352243291/1099511627776)
  R := (38212162441/100000000000000)
  total := (388120653877/100000000000000)
  k := 0
  n := 32
  sFloor := (2187818638975/1152921504606846976)
  nFloor := 77179456528663400429499247662408679361747630283291078164480
  eFloor := 77093794416215544721619481975497509731885784047518369185792
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1388707,width:=277741,den:=32768,localDen:=7083549724304467820544,lowerC:=7088965348522620616704,s:=[46422344674037760,-26583357412448256,7044928174141440],L:=[7091327571797204821293,-3085027072049938432,910819988820983808,-222563856658989056,34547668957003776],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor479Source.source.poly i) 1388707 277741 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor479Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 10) (CoreQuotient.fused G u 4 10) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 4 10 WideAnchor479Source.data
    WideAnchor479Source.path_checked WideAnchor479Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor479Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 4) (CoreQuotient.fused G u 10 4) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 10 4 WideAnchor479Source.data
    WideAnchor479Source.path_swapped WideAnchor479Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor479Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor479Cell127
