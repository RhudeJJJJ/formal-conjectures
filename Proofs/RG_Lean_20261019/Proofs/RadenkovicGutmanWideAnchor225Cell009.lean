/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor225Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor225Cell009
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1352601/70368744177664)
  b := (1623121/70368744177664)
  s := [(4398046511103/4398046511104)]
  L := [(2864364576833/309485009821345068724781056),(1718617475495/464227514732017603087171584),(171861620507/464227514732017603087171584),(-1/14507109835375550096474112),(1/29014219670751100192948224)]
  c := (44755696513/4835703278458516698824704)
  R := (-1615679211798493/100000000000000)
  total := (-61751549/1000000000000000)
  k := 47
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (1335795332483/154742504910672534362390528)
  eFloor := (1466659513961/154742504910672534362390528)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1352601,width:=270520,den:=70368744177664,localDen:=928455029464035206174343168,lowerC:=8593093730496,s:=[928455029463824099941810176],L:=[8593093730499,3437234950990,343723241014,-64,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor225Source.source.poly i) 1352601 270520 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor225Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 10) (CoreQuotient.fused G u 0 10) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 0 10 WideAnchor225Source.data
    WideAnchor225Source.path_checked WideAnchor225Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor225Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 0) (CoreQuotient.fused G u 10 0) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 10 0 WideAnchor225Source.data
    WideAnchor225Source.path_swapped WideAnchor225Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor225Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor225Cell009
