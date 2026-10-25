/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor015Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor015Cell063
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1557865/4294967296)
  b := (934719/2147483648)
  s := [(2194267345713/2199023255552),(-474042479/549755813888),(-93100797/1099511627776)]
  L := [(354123991307741840064599/309485009821345068724781056),(6169481387483/13510798882111488),(305614771691/6755399441055744),(-71108879/844424930131968),(-1711235/422212465065984)]
  c := (322073893865/281474976710656)
  R := (-16932544566653/5000000000000)
  total := (-238888042823/1000000000000000)
  k := 10
  n := 32
  sFloor := (2192184974203/4398046511104)
  nFloor := (184319548775/18014398509481984)
  eFloor := (697524295737/72057594037927936)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1557865,width:=311573,den:=4294967296,localDen:=928455029464035206174343168,lowerC:=1062371973922982429982720,s:=[926447025047279449084526592,-800586574418319815737344,-78616634001955535978496],L:=[1062371973923225520193797,423963532680323020095488,42003374386795251761152,-78185039298616623104,-3763045560714526720],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor015Source.source.poly i) 1557865 311573 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor015Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 24) (CoreQuotient.fused G u 9 24) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 24 WideAnchor015Source.data
    WideAnchor015Source.path_checked WideAnchor015Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor015Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 24 9) (CoreQuotient.fused G u 24 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 24 9 WideAnchor015Source.data
    WideAnchor015Source.path_swapped WideAnchor015Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor015Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor015Cell063
