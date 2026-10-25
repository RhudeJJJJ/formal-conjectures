/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor243Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor243Cell059
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (375643/2147483648)
  b := (901543/4294967296)
  s := [(1099442182913/1099511627776),(-27774427/1099511627776),(-2775507/1099511627776)]
  L := [(177349954794825260763705725/5070602400912917605986812821504),(1008016914989/72057594037927936),(151142630719/108086391056891904),(-497445/4503599627370496),(-37255/6755399441055744)]
  c := (315036805167/9007199254740992)
  R := (-513042262946527/100000000000000)
  total := (-176206122939/1000000000000000)
  k := 15
  n := 32
  sFloor := (1099411632979/2199023255552)
  nFloor := (35276869151/18014398509481984)
  eFloor := (509638830337/288230376151711744)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=751286,width:=150257,den:=4294967296,localDen:=15211807202738752817960438464512,lowerC:=532049864384284780828557312,s:=[15210846429027506701675115053056,-384260809997196420420993024,-38399300477842032357801984],L:=[532049864384475782291117175,212798653252857063001817088,21271434230808902560120832,-1680219837477987287040,-83890802058843914240],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor243Source.source.poly i) 751286 150257 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor243Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 25) (CoreQuotient.fused G u 0 25) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 25 WideAnchor243Source.data
    WideAnchor243Source.path_checked WideAnchor243Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor243Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 25 0) (CoreQuotient.fused G u 25 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 25 0 WideAnchor243Source.data
    WideAnchor243Source.path_swapped WideAnchor243Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor243Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor243Cell059
