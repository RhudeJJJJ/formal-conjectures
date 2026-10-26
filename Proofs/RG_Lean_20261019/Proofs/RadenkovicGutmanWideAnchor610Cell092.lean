/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor610Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor610Cell092
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1203765/16777216)
  b := (722259/8388608)
  s := [(7128395036865/8796093022208),(-507929154665/8796093022208),(2062163363/4398046511104)]
  L := [(291837764099780861/4611686018427387904),(350639331137/13194139533312),(18333139735/6597069766656),(-147364201/1649267441664),(-13500107/824633720832)]
  c := (1113272720717/17592186044416)
  R := (-69003768858509/50000000000000)
  total := (-18399131974763/1000000000000000)
  k := 4
  n := 32
  sFloor := (1656147552231/4398046511104)
  nFloor := (600149412057/4398046511104)
  eFloor := (993183551959/4398046511104)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1203765,width:=240753,den:=16777216,localDen:=13835058055282163712,lowerC:=875513292298911744,s:=[11211995931263631360,-798903481923010560,6487005031563264],L:=[875513292299342583,367671987286310912,38447380661534720,-1236180515422208,-226494211162112],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor610Source.source.poly i) 1203765 240753 16777216
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor610Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 8) (CoreQuotient.fused G u 6 8) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 6 8 WideAnchor610Source.data
    WideAnchor610Source.path_checked WideAnchor610Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor610Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 6) (CoreQuotient.fused G u 8 6) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 8 6 WideAnchor610Source.data
    WideAnchor610Source.path_swapped WideAnchor610Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor610Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor610Cell092
