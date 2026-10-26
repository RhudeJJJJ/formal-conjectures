/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor520Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor520Cell111
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (600901/262144)
  b := (721081/262144)
  s := [(1662606688797/70368744177664),(-2790908127217/281474976710656),(283582260909/140737488355328)]
  L := [(86049597645730018393/73786976294838206464),(-333068543915/13194139533312),(-6804025123/6597069766656),(1104810887/824633720832),(-109297325/412316860416)]
  c := (627265415327/549755813888)
  R := (52758222441/800000000000)
  total := (4091262688989/125000000000000)
  k := 0
  n := 32
  sFloor := (1106670787447/140737488355328)
  nFloor := (874735408939/4)
  eFloor := (715453607983/4)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=600901,width:=120180,den:=262144,localDen:=221360928884514619392,lowerC:=252570416694498951168,s:=[5230108413936009216,-2194859460303519744,446036329222373376],L:=[258148792937190055179,-5587962904067440640,-228305198315995136,296570414245609472,-58678554551910400],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor520Source.source.poly i) 600901 120180 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor520Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 5) (CoreQuotient.fused G u 4 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 5 WideAnchor520Source.data
    WideAnchor520Source.path_checked WideAnchor520Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor520Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 4) (CoreQuotient.fused G u 5 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 4 WideAnchor520Source.data
    WideAnchor520Source.path_swapped WideAnchor520Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor520Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor520Cell111
