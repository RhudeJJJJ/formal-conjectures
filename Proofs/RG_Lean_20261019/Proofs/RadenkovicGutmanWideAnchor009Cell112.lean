/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor009Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor009Cell112
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (721081/262144)
  b := (865297/262144)
  s := [(1106658787727/70368744177664),(-999148354971/140737488355328),(54064813251/35184372088832)]
  L := [(21047505943858690315/18446744073709551616),(-6022742903/206158430208),(3475328629/1649267441664),(110695661/206158430208),(-16822831/103079215104)]
  c := (1225135638789/1099511627776)
  R := (338079552937/6250000000000)
  total := (8231437676413/250000000000000)
  k := 0
  n := 32
  sFloor := (1430428473487/281474976710656)
  nFloor := 3403144712942668917930662559744
  eFloor := 2890269861250804768618955407360
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=721081,width:=144216,den:=262144,localDen:=55340232221128654848,lowerC:=61663095723783094272,s:=[870311883749720064,-392881119548276736,85036598429220864],L:=[63142517831576070945,-1616717737537568768,116612678159433728,29714640237756416,-9031688621391872],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor009Source.source.poly i) 721081 144216 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor009Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 18) (CoreQuotient.fused G u 9 18) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 18 WideAnchor009Source.data
    WideAnchor009Source.path_checked WideAnchor009Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor009Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 18 9) (CoreQuotient.fused G u 18 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 18 9 WideAnchor009Source.data
    WideAnchor009Source.path_swapped WideAnchor009Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor009Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor009Cell112
