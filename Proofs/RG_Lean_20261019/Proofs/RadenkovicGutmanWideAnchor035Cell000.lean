/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor035Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor035Cell000
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1/268435456)
  b := (1258291/281474976710656)
  s := [(4398046511103/4398046511104)]
  L := [(652593471341252308153320601/1393796574908163946345982392040522594123776),(463695108255/2475880078570760549798248448),(8694274985/464227514732017603087171584),(3/309485009821345068724781056),(-1/232113757366008801543585792)]
  c := (289809719041/618970019642690137449562112)
  R := (-1764880433325051/100000000000000)
  total := (-817471/62500000000000)
  k := 51
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (156307360081/309485009821345068724781056)
  eFloor := (232268891189/309485009821345068724781056)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1048576,width:=209715,den:=281474976710656,localDen:=4181389724724491839037947176121567782371328,lowerC:=1957780414022093609059221504,s:=[4181389724723541101087776004070445254967296],L:=[1957780414023756924459961803,783111418781527426392391680,78311067165405249399685120,40532396646334464,-18014398509481984],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor035Source.source.poly i) 1048576 209715 281474976710656
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor035Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 14) (CoreQuotient.fused G u 10 14) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 14 WideAnchor035Source.data
    WideAnchor035Source.path_checked WideAnchor035Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor035Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 10) (CoreQuotient.fused G u 14 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 14 10 WideAnchor035Source.data
    WideAnchor035Source.path_swapped WideAnchor035Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor035Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor035Cell000
