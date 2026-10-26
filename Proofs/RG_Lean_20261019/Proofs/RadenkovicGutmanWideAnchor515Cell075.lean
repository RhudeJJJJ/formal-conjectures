/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor515Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor515Cell075
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (868127/268435456)
  b := (130219/33554432)
  s := [(2198427063097/2199023255552),(-29799655/274877906944),(-11897867/1099511627776)]
  L := [(116050742129239935834802711/633825300114114700748351602688),(2638156548127/36028797018963968),(131802399851/18014398509481984),(-2626905/2251799813685248),(-65455/1125899906842624)]
  c := (824590117995/4503599627370496)
  R := (-430275055798403/100000000000000)
  total := (-544484293163/200000000000000)
  k := 13
  n := 32
  sFloor := (2198164870123/4398046511104)
  nFloor := (1470456984031/4503599627370496)
  eFloor := (544414283843/2251799813685248)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=868127,width:=173625,den:=268435456,localDen:=633825300114114700748351602688,lowerC:=116050742129239854006927360,s:=[633653459338551238271243911168,-68713326158729901045186560,-6858653361626076304900096],L:=[116050742129239935834802711,46410940808944496863608832,4637384678558599355564032,-739408023696105799680,-36847889201191976960],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor515Source.source.poly i) 868127 173625 268435456
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor515Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 4 WideAnchor515Source.data
    WideAnchor515Source.path_checked WideAnchor515Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor515Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 4 WideAnchor515Source.data
    WideAnchor515Source.path_swapped WideAnchor515Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor515Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor515Cell075
