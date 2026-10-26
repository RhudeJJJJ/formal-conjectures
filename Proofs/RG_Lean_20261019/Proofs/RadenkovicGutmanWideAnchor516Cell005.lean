/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor516Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor516Cell005
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (652297/70368744177664)
  b := (195689/17592186044416)
  s := [(4398046511103/4398046511104)]
  L := [(366079703276445748154448339/348449143727040986586495598010130648530944),(520228952677/1237940039285380274899124224),(39017051807/928455029464035206174343168),(3/154742504910672534362390528),(-1/116056878683004400771792896)]
  c := (1300576369361/1237940039285380274899124224)
  R := (-86223544018019/5000000000000)
  total := (-31796777/1000000000000000)
  k := 50
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (1211058902563/618970019642690137449562112)
  eFloor := (1188316772701/618970019642690137449562112)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=652297,width:=130459,den:=70368744177664,localDen:=1045347431181122959759486794030391945592832,lowerC:=1098239109828951032041832448,s:=[1045347431180885275271944001017611313741824],L:=[1098239109829337244463345017,439294297016902612036878336,43929294994775134403821568,20266198323167232,-9007199254740992],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor516Source.source.poly i) 652297 130459 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor516Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((25/13) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (25/13) 4 4 WideAnchor516Source.data
    WideAnchor516Source.path_checked WideAnchor516Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor516Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((25/13) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (25/13) 4 4 WideAnchor516Source.data
    WideAnchor516Source.path_swapped WideAnchor516Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor516Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor516Cell005
