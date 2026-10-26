/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor540Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor540Cell057
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (521727/4294967296)
  b := (78259/536870912)
  s := [(1098895207915/1099511627776),(-123182081/549755813888),(-24523907/1099511627776)]
  L := [(717912293627760277260023/2475880078570760549798248448),(6264545071925/54043195528445952),(312500539637/27021597764222976),(-18113777/3377699720527872),(-448541/1688849860263936)]
  c := (10202147303/35184372088832)
  R := (-203643976755379/50000000000000)
  total := (-12084216111/125000000000000)
  k := 12
  n := 32
  sFloor := (549312159923/1099511627776)
  nFloor := (946974514321/1152921504606846976)
  eFloor := (915724984411/1152921504606846976)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=521727,width:=104345,den:=4294967296,localDen:=7427640235712281649394745344,lowerC:=2153736880882955191320576,s:=[7423476073327826589985013760,-1664288322270966765846528,-165668787640303047671808],L:=[2153736880883280831780069,860992518663546968473600,85899494254289069539328,-39832616868882939904,-1972704180137099264],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor540Source.source.poly i) 521727 104345 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor540Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 18) (CoreQuotient.fused G u 5 18) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 18 WideAnchor540Source.data
    WideAnchor540Source.path_checked WideAnchor540Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor540Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 18 5) (CoreQuotient.fused G u 18 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 18 5 WideAnchor540Source.data
    WideAnchor540Source.path_swapped WideAnchor540Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor540Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor540Cell057
