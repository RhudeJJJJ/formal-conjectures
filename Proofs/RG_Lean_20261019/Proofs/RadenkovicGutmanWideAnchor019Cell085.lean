/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor019Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor019Cell085
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (671899/33554432)
  b := (1612557/67108864)
  s := [(5356415974777/17592186044416),(-594021490869/17592186044416),(55789689831/8796093022208)]
  L := [(339046172072272493083/590295810358705651712),(1200001098989/26388279066624),(-117569575681/13194139533312),(2116861351/1649267441664),(-105788231/824633720832)]
  c := (1263045415551/2199023255552)
  R := (-13862187145867/50000000000000)
  total := (-1041897815461/1000000000000000)
  k := 1
  n := 32
  sFloor := (304623366473/2199023255552)
  nFloor := (1379612006237/35184372088832)
  eFloor := (1280686574269/35184372088832)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1343798,width:=268759,den:=67108864,localDen:=1770887431076116955136,lowerC:=1017138516216426528768,s:=[539194486768105684992,-59796161165707444224,11231948122412285952],L:=[1017138516216817479249,80530710551903338496,-15779921329827872768,2272962568177844224,-227178496223346688],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor019Source.source.poly i) 1343798 268759 67108864
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor019Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 28) (CoreQuotient.fused G u 9 28) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 28 WideAnchor019Source.data
    WideAnchor019Source.path_checked WideAnchor019Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor019Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 28 9) (CoreQuotient.fused G u 28 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 28 9 WideAnchor019Source.data
    WideAnchor019Source.path_swapped WideAnchor019Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor019Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor019Cell085
