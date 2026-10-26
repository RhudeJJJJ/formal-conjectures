/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor040Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor040Cell094
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (433355/4194304)
  b := (260013/2097152)
  s := [(931124096619/2199023255552),(-300271396801/17592186044416),(-7874880579/8796093022208)]
  L := [(264608017063551503095/590295810358705651712),(1406075244595/52776558133248),(64336147765/26388279066624),(-1225892689/3298534883328),(3066071/1649267441664)]
  c := (492870839431/1099511627776)
  R := (-1002967793397/2500000000000)
  total := (-3986558855313/500000000000000)
  k := 2
  n := 32
  sFloor := (445810725937/2199023255552)
  nFloor := (932684434615/274877906944)
  eFloor := (210698448241/68719476736)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=433355,width:=86671,den:=4194304,localDen:=1770887431076116955136,lowerC:=793824051190579593216,s:=[749840164405527969792,-30226308496512516096,-1585422869377056768],L:=[793824051190654509285,47180056181646295040,4317525790645288960,-658146125957562368,3292168668053504],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor040Source.source.poly i) 433355 86671 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor040Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 19) (CoreQuotient.fused G u 10 19) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 19 WideAnchor040Source.data
    WideAnchor040Source.path_checked WideAnchor040Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor040Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 19 10) (CoreQuotient.fused G u 19 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 19 10 WideAnchor040Source.data
    WideAnchor040Source.path_swapped WideAnchor040Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor040Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor040Cell094
