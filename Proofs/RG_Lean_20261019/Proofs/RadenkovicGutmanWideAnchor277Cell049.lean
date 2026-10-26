/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor277Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor277Cell049
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (970699/34359738368)
  b := (582419/17179869184)
  s := [(2198957831509/2199023255552),(-13084183/1099511627776),(-1308095/1099511627776)]
  L := [(640950928990921627641916061/40564819207303340847894502572032),(683110681777/108086391056891904),(4268898113/6755399441055744),(-52601/3377699720527872),(-2629/3377699720527872)]
  c := (35579923951/2251799813685248)
  R := (-552772941339203/100000000000000)
  total := (-6140625539/200000000000000)
  k := 16
  n := 32
  sFloor := (2198929046953/4398046511104)
  nFloor := (1125517297877/73786976294838206464)
  eFloor := (264911594401/18446744073709551616)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=970699,width:=194139,den:=34359738368,localDen:=121694457621910022543683507716096,lowerC:=1922852786971130229373796352,s:=[121690837040177557437060200005632,-1448163451287487573150138368,-144780562134594575526789120],L:=[1922852786972764882925748183,769114252975925668083662848,76901631803957654105096192,-1895150751994523680768,-94719707362856271872],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor277Source.source.poly i) 970699 194139 34359738368
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor277Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 5) (CoreQuotient.fused G u 0 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 5 WideAnchor277Source.data
    WideAnchor277Source.path_checked WideAnchor277Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor277Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 0) (CoreQuotient.fused G u 5 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 0 WideAnchor277Source.data
    WideAnchor277Source.path_swapped WideAnchor277Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor277Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor277Cell049
