/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor521Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor521Cell074
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1446879/536870912)
  b := (868127/268435456)
  s := [(68703134221/68719476736),(-418242729/4398046511104),(-20877539/2199023255552)]
  L := [(183805152137601389508254115/1267650600228229401496703205376),(261158868295/4503599627370496),(156591131687/27021597764222976),(-432151/562949953421312),(-64643/1688849860263936)]
  c := (653007078233/4503599627370496)
  R := (-441939979169629/100000000000000)
  total := (-18652455539/8000000000000)
  k := 13
  n := 32
  sFloor := (274783787021/549755813888)
  nFloor := (1075826256067/4503599627370496)
  eFloor := (1764715568739/9007199254740992)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1446879,width:=289375,den:=536870912,localDen:=3802951800684688204490109616128,lowerC:=551415456412581586790252544,s:=[3802047402109510926131326353408,-361650777307165313495728128,-36105245514552191112708096],L:=[551415456412804168524762345,220529059113349207881154560,22038242572346795896078336,-2919352623851680825344,-145563095356055486464],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor521Source.source.poly i) 1446879 289375 536870912
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor521Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 6) (CoreQuotient.fused G u 4 6) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 6 WideAnchor521Source.data
    WideAnchor521Source.path_checked WideAnchor521Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor521Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 4) (CoreQuotient.fused G u 6 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 6 4 WideAnchor521Source.data
    WideAnchor521Source.path_swapped WideAnchor521Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor521Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor521Cell074
