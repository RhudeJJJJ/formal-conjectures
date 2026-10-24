/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor005Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor005Cell085
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (671899/33554432)
  b := (1612557/67108864)
  s := [(6262965674473/17592186044416),(-667811954223/17592186044416),(61651031543/8796093022208)]
  L := [(294176747067662001999/590295810358705651712),(1183069547323/26388279066624),(-116245030519/13194139533312),(1938242279/1649267441664),(-86197805/824633720832)]
  c := (273973445471/549755813888)
  R := (-6964430175393/20000000000000)
  total := (-1317157917661/1000000000000000)
  k := 2
  n := 32
  sFloor := (714806972917/4398046511104)
  nFloor := (417790825377/17592186044416)
  eFloor := (796284143933/35184372088832)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1343798,width:=268759,den:=67108864,localDen:=1770887431076116955136,lowerC:=882530241202788237312,s:=[630450767527315243008,-67224152420288299008,12411992073836691456],L:=[882530241202986005997,79394453353840771072,-15602143887550840832,2081171800007376896,-185108376730992640],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor005Source.source.poly i) 1343798 268759 67108864
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor005Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 14) (CoreQuotient.fused G u 9 14) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 14 WideAnchor005Source.data
    WideAnchor005Source.path_checked WideAnchor005Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor005Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 9) (CoreQuotient.fused G u 14 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 14 9 WideAnchor005Source.data
    WideAnchor005Source.path_swapped WideAnchor005Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor005Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor005Cell085
