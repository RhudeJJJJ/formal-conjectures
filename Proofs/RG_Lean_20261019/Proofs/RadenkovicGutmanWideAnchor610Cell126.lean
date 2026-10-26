/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor610Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor610Cell126
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (144657/4096)
  b := (1388707/32768)
  s := [(6521463787899/576460752303423488),(-933042031741/144115188075855872),(123570552495/72057594037927936)]
  L := [(2364904125416101588485/2361183241434822606848),(-8228997979/13194139533312),(403915373/2199023255552),(-36921083/824633720832),(953431/137438953472)]
  c := (34397465831/34359738368)
  R := (54870565529/100000000000000)
  total := (928516059679/200000000000000)
  k := 0
  n := 32
  sFloor := (1888930040447/576460752303423488)
  nFloor := 109849035934445410127829788029230096435044213300238745600
  eFloor := 109673719897031231988659879062433327135840367208690614272
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1157256,width:=231451,den:=32768,localDen:=7083549724304467820544,lowerC:=7091327558852278222848,s:=[80135747025702912,-45860881944133632,12147479592468480],L:=[7094712376248304765455,-4417909649831886848,1301102488039981056,-317149688035803136,49139459567910912],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor610Source.source.poly i) 1157256 231451 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor610Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 8) (CoreQuotient.fused G u 6 8) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 6 8 WideAnchor610Source.data
    WideAnchor610Source.path_checked WideAnchor610Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor610Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 6) (CoreQuotient.fused G u 8 6) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 8 6 WideAnchor610Source.data
    WideAnchor610Source.path_swapped WideAnchor610Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor610Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor610Cell126
