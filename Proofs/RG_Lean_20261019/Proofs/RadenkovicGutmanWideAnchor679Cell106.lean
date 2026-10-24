/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor679Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor679Cell106
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (241489/262144)
  b := (1159147/1048576)
  s := [(1887741577883/17592186044416),(-1827994971745/70368744177664),(115538053665/35184372088832)]
  L := [(653777391920258533113/590295810358705651712),(351412871869/6597069766656),(-43494014555/3298534883328),(619967909/412316860416),(-19512325/206158430208)]
  c := (1217755287737/1099511627776)
  R := (5107156472233/100000000000000)
  total := (11264817993921/1000000000000000)
  k := 0
  n := 32
  sFloor := (1488511861779/35184372088832)
  nFloor := (1016972633575/16384)
  eFloor := (740260026973/16384)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=965956,width:=193191,den:=1048576,localDen:=1770887431076116955136,lowerC:=1961332175760556818432,s:=[190026289225943482368,-46002999731819642880,5815220647671889920],L:=[1961332175760775599339,94331674504424587264,-23350671260684124160,2662741893724504064,-167609595487846400],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor679Source.source.poly i) 965956 193191 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor679Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 8) (CoreQuotient.fused G u 8 8) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 8 8 WideAnchor679Source.data
    WideAnchor679Source.path_checked WideAnchor679Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor679Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 8) (CoreQuotient.fused G u 8 8) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 8 8 WideAnchor679Source.data
    WideAnchor679Source.path_swapped WideAnchor679Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor679Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor679Cell106
