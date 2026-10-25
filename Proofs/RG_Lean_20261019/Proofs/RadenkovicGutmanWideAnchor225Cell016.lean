/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor225Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor225Cell016
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (302913/4398046511104)
  b := (726991/8796093022208)
  s := [(2199023255551/2199023255552)]
  L := [(646970509301920479038845583/5444517870735015415413993718908291383296),(459699436839/9671406556917033397649408),(45969867785/9671406556917033397649408),(1/302231454903657293676544),(-1/604462909807314587353088)]
  c := (4489259723/37778931862957161709568)
  R := (-93003390278973/6250000000000)
  total := (-50921581/250000000000000)
  k := 43
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (1071905058173/9671406556917033397649408)
  eFloor := (1176916637903/9671406556917033397649408)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=605826,width:=121165,den:=8796093022208,localDen:=5444517870735015415413993718908291383296,lowerC:=646970509301509634922643456,s:=[5444517870732539535335422958358493134848],L:=[646970509301920479038845583,258787776556318407700512768,25878734928349621041233920,18014398509481984,-9007199254740992],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor225Source.source.poly i) 605826 121165 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor225Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 10) (CoreQuotient.fused G u 0 10) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 0 10 WideAnchor225Source.data
    WideAnchor225Source.path_checked WideAnchor225Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor225Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 0) (CoreQuotient.fused G u 10 0) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 10 0 WideAnchor225Source.data
    WideAnchor225Source.path_swapped WideAnchor225Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor225Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor225Cell016
