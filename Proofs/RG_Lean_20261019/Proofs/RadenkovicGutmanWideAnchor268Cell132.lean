/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor268Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor268Cell132
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (863885/8192)
  b := (518331/4096)
  s := [(1965674335441/4611686018427387904),(-4508070429005/18446744073709551616),(597964965109/9223372036854775808)]
  L := [(1180802885866259852919/1180591620717411303424),(-470856389/6597069766656),(34966565/1649267441664),(-1074341/206158430208),(20935/25769803776)]
  c := (274912095541/274877906944)
  R := (1243696571/20000000000000)
  total := (1573144558333/1000000000000000)
  k := 0
  n := 32
  sFloor := (142204901343/1152921504606846976)
  nFloor := 330455710325422524284132593779259306760702229359370116729471558996010110643758161300089418583659118954316844079430492538526553786719587653691589461995975464333041633858550983241128601945995476992
  eFloor := 330396304449835915067605116028736427494307660991710013319814433147954628197838119116642003662330786199948831501915706040957911920976277337910691325624165225224841659217037631891983132354909569024
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=863885,width:=172777,den:=8192,localDen:=3541774862152233910272,lowerC:=3542215378870267281408,s:=[1509637889618688,-865549522368960,229618546601856],L:=[3542408657598779558757,-252789098983456768,75090126564229120,-18457037839007744,2877284490936320],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor268Source.source.poly i) 863885 172777 8192
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor268Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 44) (CoreQuotient.fused G u 0 44) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 44 WideAnchor268Source.data
    WideAnchor268Source.path_checked WideAnchor268Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor268Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 44 0) (CoreQuotient.fused G u 44 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 44 0 WideAnchor268Source.data
    WideAnchor268Source.path_swapped WideAnchor268Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor268Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor268Cell132
