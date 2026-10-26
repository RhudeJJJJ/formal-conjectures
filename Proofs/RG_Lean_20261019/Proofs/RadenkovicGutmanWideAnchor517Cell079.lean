/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor517Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor517Cell079
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (900073/134217728)
  b := (1080087/134217728)
  s := [(4393374308329/4398046511104),(-1866666575/4398046511104),(-92721419/2199023255552)]
  L := [(8679667634305095102554027/19807040628566084398385987584),(1183982963911/6755399441055744),(118345799773/6755399441055744),(-327497/211106232532992),(-34081/422212465065984)]
  c := (1973527931637/4503599627370496)
  R := (-386640475190881/100000000000000)
  total := (-2529978619893/500000000000000)
  k := 12
  n := 32
  sFloor := (1097830549729/2199023255552)
  nFloor := (459099360237/562949953421312)
  eFloor := (556782784599/562949953421312)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=900073,width:=180014,den:=134217728,localDen:=59421121885698253195157962752,lowerC:=26039002902907203820191744,s:=[59357996693668785003064983552,-25220156674784880073113600,-2505480888345981767122944],L:=[26039002902915285307662081,10414424287270693385535488,1040980663590910410358784,-92182210447809708032,-4796474340637933568],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor517Source.source.poly i) 900073 180014 134217728
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor517Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 4 4 WideAnchor517Source.data
    WideAnchor517Source.path_checked WideAnchor517Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor517Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 4 4 WideAnchor517Source.data
    WideAnchor517Source.path_swapped WideAnchor517Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor517Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor517Cell079
