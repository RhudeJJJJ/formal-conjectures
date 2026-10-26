/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor282Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor282Cell065
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (560831/1073741824)
  b := (672997/1073741824)
  s := [(2199006384017/2199023255552),(-3374263/1099511627776),(-84351/274877906944)]
  L := [(3603342378687315687289857809/649037107316853453566312041152512),(120014318369/54043195528445952),(32002824787/144115188075855872),(-70229/54043195528445952),(-585/9007199254740992)]
  c := (800102734885/144115188075855872)
  R := (-605069165847063/100000000000000)
  total := (-155570076179/250000000000000)
  k := 18
  n := 32
  sFloor := (2198998960683/4398046511104)
  nFloor := (657489867075/72057594037927936)
  eFloor := (908614150593/144115188075855872)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=560831,width:=112166,den:=1073741824,localDen:=1947111321950560360698936123457536,lowerC:=10810027136058602252276858880,s:=[1947096383155923130301499788230656,-5975439935845191625388064768,-597504502794806165130706944],L:=[10810027136061947061869573427,4323971515886019786091528192,432383729356609419063853056,-2530266385844820508672,-126461077536563527680],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor282Source.source.poly i) 560831 112166 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor282Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 8) (CoreQuotient.fused G u 0 8) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 8 WideAnchor282Source.data
    WideAnchor282Source.path_checked WideAnchor282Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor282Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 0) (CoreQuotient.fused G u 8 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 8 0 WideAnchor282Source.data
    WideAnchor282Source.path_swapped WideAnchor282Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor282Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor282Cell065
