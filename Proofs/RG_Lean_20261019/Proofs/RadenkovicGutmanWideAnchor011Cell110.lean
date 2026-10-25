/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor011Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor011Cell110
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (500751/262144)
  b := (600901/262144)
  s := [(1208666463789/35184372088832),(-3720028480325/281474976710656),(350420277039/140737488355328)]
  L := [(43730894922534106751/36893488147419103232),(-104620329433/6597069766656),(-1034745599/206158430208),(847187959/412316860416),(-16656109/51539607552)]
  c := (641115350791/549755813888)
  R := (3843379756787/50000000000000)
  total := (15497186594541/500000000000000)
  k := 0
  n := 32
  sFloor := (51954248313/4398046511104)
  nFloor := 3841616641052542008033280
  eFloor := 3025697323979629320470528
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=500751,width:=100150,den:=262144,localDen:=110680464442257309696,lowerC:=129073568653636534272,s:=[3802135937802043392,-1462774718919475200,275581719312334848],L:=[131192684767602320253,-1755237864888598528,-555524813423116288,227415286091874304,-35768721716805632],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor011Source.source.poly i) 500751 100150 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor011Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 20) (CoreQuotient.fused G u 9 20) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 20 WideAnchor011Source.data
    WideAnchor011Source.path_checked WideAnchor011Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor011Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 20 9) (CoreQuotient.fused G u 20 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 20 9 WideAnchor011Source.data
    WideAnchor011Source.path_swapped WideAnchor011Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor011Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor011Cell110
