/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor530Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor530Cell113
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (865297/262144)
  b := (259589/65536)
  s := [(5665833108217/562949953421312),(-168883322089/35184372088832),(38337265759/35184372088832)]
  L := [(163989869496397426775/147573952589676412928),(-178906843987/6597069766656),(11370478661/3298534883328),(-4794149/412316860416),(-14676893/206158430208)]
  c := (149462628853/137438953472)
  R := (4193327179149/100000000000000)
  total := (3887114284407/125000000000000)
  k := 0
  n := 32
  sFloor := (447137025867/140737488355328)
  nFloor := 1025499864615616512
  eFloor := 904453023883853824
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=865297,width:=173059,den:=262144,localDen:=442721857769029238784,lowerC:=481452827173365743616,s:=[4455792462961311744,-2125043980113543168,482394441366110208],L:=[491969608489192280325,-12006235061792800768,1526119812151902208,-5147678291787776,-31518387720945664],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor530Source.source.poly i) 865297 173059 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor530Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 8) (CoreQuotient.fused G u 4 8) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 4 8 WideAnchor530Source.data
    WideAnchor530Source.path_checked WideAnchor530Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor530Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 4) (CoreQuotient.fused G u 8 4) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 8 4 WideAnchor530Source.data
    WideAnchor530Source.path_swapped WideAnchor530Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor530Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor530Cell113
