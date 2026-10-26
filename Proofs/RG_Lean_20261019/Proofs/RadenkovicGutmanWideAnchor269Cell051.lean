/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor269Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor269Cell051
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1397805/34359738368)
  b := (838683/17179869184)
  s := [(4398039815499/4398046511104),(-2678231/4398046511104),(-133909/2199023255552)]
  L := [(3864986346769/4611686018427387904),(4637969160911/13835058055282163712),(231895567015/6917529027641081856),(-72275/864691128455135232),(-1807/432345564227567616)]
  c := (241561646673/288230376151711744)
  R := (-174901824116073/25000000000000)
  total := (-56159487743/1000000000000000)
  k := 21
  n := 32
  sFloor := (2199018434725/4398046511104)
  nFloor := (1631625231985/9223372036854775808)
  eFloor := (740973172459/4611686018427387904)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1397805,width:=279561,den:=34359738368,localDen:=13835058055282163712,lowerC:=11594959040304,s:=[13835036992730038272,-8424986247168,-842482581504],L:=[11594959040307,4637969160911,463791134030,-1156400,-57824],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor269Source.source.poly i) 1397805 279561 34359738368
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor269Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 45) (CoreQuotient.fused G u 0 45) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 45 WideAnchor269Source.data
    WideAnchor269Source.path_checked WideAnchor269Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor269Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 45 0) (CoreQuotient.fused G u 45 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 45 0 WideAnchor269Source.data
    WideAnchor269Source.path_swapped WideAnchor269Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor269Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor269Cell051
