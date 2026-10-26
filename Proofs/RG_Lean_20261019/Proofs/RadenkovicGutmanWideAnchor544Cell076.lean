/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor544Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor544Cell076
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (130219/33554432)
  b := (625051/134217728)
  s := [(1474360847719/2199023255552),(-637119996289/8796093022208),(22504347995/4398046511104)]
  L := [(7555881574420860517/36893488147419103232),(2845009677845/52776558133248),(-4661798287/3298534883328),(-545268829/1649267441664),(44268379/824633720832)]
  c := (1801462548833/8796093022208)
  R := (-79285439301951/100000000000000)
  total := (-569155423173/1000000000000000)
  k := 3
  n := 32
  sFloor := (331583255661/1099511627776)
  nFloor := (1089499442187/1125899906842624)
  eFloor := (1049448008805/1125899906842624)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=520876,width:=104175,den:=134217728,localDen:=110680464442257309696,lowerC:=22667644723261341696,s:=[74207011212374310912,-8016824846744813568,566340460876922880],L:=[22667644723262581551,5966417735911997440,-156423993618857984,-36592371688800256,5941601251622912],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor544Source.source.poly i) 520876 104175 134217728
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor544Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 22) (CoreQuotient.fused G u 5 22) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 22 WideAnchor544Source.data
    WideAnchor544Source.path_checked WideAnchor544Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor544Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 22 5) (CoreQuotient.fused G u 22 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 22 5 WideAnchor544Source.data
    WideAnchor544Source.path_swapped WideAnchor544Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor544Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor544Cell076
