/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor503Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor503Cell097
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (748837/4194304)
  b := (224651/1048576)
  s := [(3772744628765/8796093022208),(-368348946127/8796093022208),(5922150973/2199023255552)]
  L := [(145331491007685571537/295147905179352825856),(582700980651/8796093022208),(-23650002859/13194139533312),(-186452495/549755813888),(53744803/824633720832)]
  c := (2165607974047/4398046511104)
  R := (-35422966306793/100000000000000)
  total := (-1440022728939/125000000000000)
  k := 2
  n := 32
  sFloor := (1714042143265/8796093022208)
  nFloor := (1382801586703/4294967296)
  eFloor := (1122375017073/4294967296)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=748837,width:=149767,den:=4194304,localDen:=885443715538058477568,lowerC:=435994473022906957824,s:=[379776909297781309440,-37079218995270254592,2384572945407148032],L:=[435994473023056714611,58656601294761885696,-1587124825464242176,-300302763105976320,57708042803740672],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor503Source.source.poly i) 748837 149767 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor503Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 33) (CoreQuotient.fused G u 4 33) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 33 WideAnchor503Source.data
    WideAnchor503Source.path_checked WideAnchor503Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor503Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 33 4) (CoreQuotient.fused G u 33 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 33 4 WideAnchor503Source.data
    WideAnchor503Source.path_swapped WideAnchor503Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor503Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor503Cell097
