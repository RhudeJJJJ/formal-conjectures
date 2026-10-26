/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor527Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor527Cell121
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (116269/8192)
  b := (558091/32768)
  s := [(385997696431/2251799813685248),(-3499333209027/36028797018963968),(459590044517/18014398509481984)]
  L := [(595847637624021348895/590295810358705651712),(-47814531205/13194139533312),(2272778977/2199023255552),(-200929793/824633720832),(5055219/137438953472)]
  c := (1106777092483/1099511627776)
  R := (164654129431/50000000000000)
  total := (1393202340829/125000000000000)
  k := 0
  n := 32
  sFloor := (1797905011451/36028797018963968)
  nFloor := 84581844689272527455173244239216640
  eFloor := 83765025859144680380363888599760896
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=465076,width:=93015,den:=32768,localDen:=1770887431076116955136,lowerC:=1782589281066169663488,s:=[303560940399624192,-171999225890095104,45179539736199168],L:=[1787542912872064046685,-6417557743720202240,1830283383234625536,-431493444863524864,65136000837353472],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor527Source.source.poly i) 465076 93015 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor527Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 7) (CoreQuotient.fused G u 4 7) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 7 WideAnchor527Source.data
    WideAnchor527Source.path_checked WideAnchor527Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor527Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 7 4) (CoreQuotient.fused G u 7 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 7 4 WideAnchor527Source.data
    WideAnchor527Source.path_swapped WideAnchor527Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor527Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor527Cell121
