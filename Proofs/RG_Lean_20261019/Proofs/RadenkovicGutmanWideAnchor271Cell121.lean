/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor271Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor271Cell121
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (116269/8192)
  b := (558091/32768)
  s := [(3103086577933/18014398509481984),(-440843814003/4503599627370496),(116082096537/4503599627370496)]
  L := [(148968744009578693641/147573952589676412928),(-3018251069/824633720832),(1155477145/1099511627776),(-102927239/412316860416),(2606005/68719476736)]
  c := (553400999747/549755813888)
  R := (5163022667/1562500000000)
  total := (1119171511157/100000000000000)
  k := 0
  n := 32
  sFloor := (1804039708069/36028797018963968)
  nFloor := 10735470592516423472443502478174580183024299316598097451948369563171837148095536059569520691703891880859840166542442496
  eFloor := 10631291033354200171250291635799858751913729245315096889583690602509197191865873762453599465048902091485667307250778112
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=465076,width:=93015,den:=32768,localDen:=442721857769029238784,lowerC:=445657349153825488896,s:=[76261455739281408,-43336710291750912,11411334417973248],L:=[446906232028736080923,-1620411204059004928,465256551473479680,-110517281343143936,16789059372318720],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor271Source.source.poly i) 465076 93015 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor271Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 47) (CoreQuotient.fused G u 0 47) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 47 WideAnchor271Source.data
    WideAnchor271Source.path_checked WideAnchor271Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor271Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 47 0) (CoreQuotient.fused G u 47 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 47 0 WideAnchor271Source.data
    WideAnchor271Source.path_swapped WideAnchor271Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor271Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor271Cell121
