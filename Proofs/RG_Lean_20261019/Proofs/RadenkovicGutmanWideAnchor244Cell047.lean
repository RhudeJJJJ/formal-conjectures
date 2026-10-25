/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor244Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor244Cell047
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (674097/34359738368)
  b := (202229/8589934592)
  s := [(4398046155247/4398046511104),(-142343/4398046511104),(-7117/2199023255552)]
  L := [(26408019417483986592779017/649037107316853453566312041152512),(3602681872837/221360928884514619392),(180133459129/110680464442257309696),(-1241/6917529027641081856),(-67/6917529027641081856)]
  c := (187640263629/4611686018427387904)
  R := (-850866635966933/100000000000000)
  total := (-33018092229/1000000000000000)
  k := 25
  n := 32
  sFloor := (2199022999335/4398046511104)
  nFloor := (827911264577/36893488147419103232)
  eFloor := (823195584359/36893488147419103232)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=674097,width:=134819,den:=34359738368,localDen:=1947111321950560360698936123457536,lowerC:=79224058252431190640295936,s:=[1947111164404888220585498297499648,-63018357400416928936230912,-6301702923484362184851456],L:=[79224058252451959778337051,31689524882896784872964096,3168941325821573714673664,-349310446097924096,-18858823439613952],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor244Source.source.poly i) 674097 134819 34359738368
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor244Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 26) (CoreQuotient.fused G u 0 26) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 26 WideAnchor244Source.data
    WideAnchor244Source.path_checked WideAnchor244Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor244Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 26 0) (CoreQuotient.fused G u 26 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 26 0 WideAnchor244Source.data
    WideAnchor244Source.path_swapped WideAnchor244Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor244Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor244Cell047
