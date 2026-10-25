/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor253Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor253Cell098
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (224651/1048576)
  b := (269581/1048576)
  s := [(1032167117443/2199023255552),(-675875976317/17592186044416),(16940324625/8796093022208)]
  L := [(312817870369869683267/590295810358705651712),(246560640689/3298534883328),(-13949535299/6597069766656),(46994953/824633720832),(-10449463/412316860416)]
  c := (582668688837/1099511627776)
  R := (-31750132368301/100000000000000)
  total := (-12185437304007/1000000000000000)
  k := 1
  n := 32
  sFloor := (1903835403119/8796093022208)
  nFloor := (236935040703/536870912)
  eFloor := (1291671785717/4294967296)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=224651,width:=44930,den:=1048576,localDen:=1770887431076116955136,lowerC:=938453611109293228032,s:=[831210752517051777024,-68035903463287160832,3410537824124928000],L:=[938453611109609049801,132371236030007738368,-3744549868975161344,100920893106028544,-44880101845762048],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor253Source.source.poly i) 224651 44930 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor253Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 30) (CoreQuotient.fused G u 0 30) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 30 WideAnchor253Source.data
    WideAnchor253Source.path_checked WideAnchor253Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor253Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 30 0) (CoreQuotient.fused G u 30 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 30 0 WideAnchor253Source.data
    WideAnchor253Source.path_swapped WideAnchor253Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor253Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor253Cell098
