/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor424Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor424Cell086
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1612557/67108864)
  b := (483767/16777216)
  s := [(4334757362635/4398046511104),(-24856556813/4398046511104),(-1120019915/2199023255552)]
  L := [(36627079733436747692197/4835703278458516698824704),(10157204107453/3377699720527872),(492758029561/1688849860263936),(-370597231/211106232532992),(-8075869/105553116266496)]
  c := (1065988318687/140737488355328)
  R := (-244149700139251/100000000000000)
  total := (-1410828594167/125000000000000)
  k := 8
  n := 32
  sFloor := (538457595749/1099511627776)
  nFloor := (1920040619787/140737488355328)
  eFloor := (1837144482241/140737488355328)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1612557,width:=322511,den:=67108864,localDen:=14507109835375550096474112,lowerC:=109881239200288575848448,s:=[14298348371414428711649280,-81990219727104758513664,-7388849519299122954240],L:=[109881239200310243076591,43624859460307504857088,4232759243611792474112,-25467247794130518016,-1109938983736967168],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor424Source.source.poly i) 1612557 322511 67108864
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor424Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((48/25) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (48/25) 2 6 WideAnchor424Source.data
    WideAnchor424Source.path_checked WideAnchor424Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor424Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((48/25) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (48/25) 6 2 WideAnchor424Source.data
    WideAnchor424Source.path_swapped WideAnchor424Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor424Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor424Cell086
