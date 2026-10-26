/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor024Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor024Cell117
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (897139/131072)
  b := (538283/65536)
  s := [(3231389714679/2251799813685248),(-881954380263/1125899906842624),(28064720933/140737488355328)]
  L := [(152977261428326063887/147573952589676412928),(-28482678423/2199023255552),(10884738217/3298534883328),(-93807929/137438953472),(18939575/206158430208)]
  c := (1128506870263/1099511627776)
  R := (1301464937389/100000000000000)
  total := (1047506208859/50000000000000)
  k := 0
  n := 32
  sFloor := (1916516489081/4503599627370496)
  nFloor := 952674533423610373363208032143965750866518501613129590499652179756448139444224
  eFloor := 916391205693380802657700900427610054665455550665559338280235108162259208110080
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=897139,width:=179427,den:=131072,localDen:=442721857769029238784,lowerC:=454396884477271867392,s:=[635317069023608832,-346798573589495808,88283978451124224],L:=[458931784284978191661,-5734320577934524416,1460924833360510976,-302176490370367488,40672427612569600],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor024Source.source.poly i) 897139 179427 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor024Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 33) (CoreQuotient.fused G u 9 33) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 33 WideAnchor024Source.data
    WideAnchor024Source.path_checked WideAnchor024Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor024Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 33 9) (CoreQuotient.fused G u 33 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 33 9 WideAnchor024Source.data
    WideAnchor024Source.path_swapped WideAnchor024Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor024Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor024Cell117
