/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor033Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor033Cell101
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1552785/4194304)
  b := (931671/2097152)
  s := [(4298877069743/17592186044416),(-1136413990527/35184372088832),(58818656535/17592186044416)]
  L := [(118027916467066297137/147573952589676412928),(2034207197453/26388279066624),(-108222606859/13194139533312),(2142462331/1649267441664),(-165394757/824633720832)]
  c := (1758753008649/2199023255552)
  R := (-279260308637/2500000000000)
  total := (-3323756918147/500000000000000)
  k := 1
  n := 32
  sFloor := (1894744365507/17592186044416)
  nFloor := (226956618403/33554432)
  eFloor := (1378554622863/268435456)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1552785,width:=310557,den:=4194304,localDen:=442721857769029238784,lowerC:=354083749401049694208,s:=[108184783734788063232,-14299397238370074624,1480219958276259840],L:=[354083749401198891411,34128333540423630848,-3631348102713049088,575112852784807936,-88795634030608384],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor033Source.source.poly i) 1552785 310557 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor033Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 12) (CoreQuotient.fused G u 10 12) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 12 WideAnchor033Source.data
    WideAnchor033Source.path_checked WideAnchor033Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor033Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 12 10) (CoreQuotient.fused G u 12 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 12 10 WideAnchor033Source.data
    WideAnchor033Source.path_swapped WideAnchor033Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor033Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor033Cell101
