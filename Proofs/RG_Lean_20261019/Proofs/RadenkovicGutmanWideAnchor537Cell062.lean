/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor537Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor537Cell062
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1298221/4294967296)
  b := (1557865/4294967296)
  s := [(2180332330485/2199023255552),(-14768616475/4398046511104),(-688631033/2199023255552)]
  L := [(6674774913338911440231/1208925819614629174706176),(1232551399395/562949953421312),(89259624103/422212465065984),(-51973117/35184372088832),(-1675657/26388279066624)]
  c := (1554092139317/281474976710656)
  R := (-64989400113141/25000000000000)
  total := (-18942601657/125000000000000)
  k := 8
  n := 32
  sFloor := (1086129695607/2199023255552)
  nFloor := (1577715500345/288230376151711744)
  eFloor := (1219585653419/288230376151711744)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1298221,width:=259644,den:=4294967296,localDen:=3626777458843887524118528,lowerC:=20024324740011572330496,s:=[3595951124676302906327040,-12178699155320025907200,-1135736742046347558912],L:=[20024324740016734320693,7940651926560838778880,766734332751276670976,-5357348106868359168,-230300544458031104],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor537Source.source.poly i) 1298221 259644 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor537Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 15) (CoreQuotient.fused G u 5 15) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 15 WideAnchor537Source.data
    WideAnchor537Source.path_checked WideAnchor537Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor537Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 15 5) (CoreQuotient.fused G u 15 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 15 5 WideAnchor537Source.data
    WideAnchor537Source.path_swapped WideAnchor537Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor537Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor537Cell062
