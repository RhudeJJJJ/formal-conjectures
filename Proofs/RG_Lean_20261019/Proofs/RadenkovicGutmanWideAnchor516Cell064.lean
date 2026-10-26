/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor516Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor516Cell064
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (934719/2147483648)
  b := (560831/1073741824)
  s := [(2199013259421/2199023255552),(-7996827/4398046511104),(-399829/2199023255552)]
  L := [(1503405940685663932463325295/649037107316853453566312041152512),(3204683162587/3458764513820540928),(1669086935/18014398509481984),(-14087/108086391056891904),(-117/18014398509481984)]
  c := (1335292712565/576460752303423488)
  R := (-648775600447087/100000000000000)
  total := (-111322668201/200000000000000)
  k := 19
  n := 32
  sFloor := (1099504430589/2199023255552)
  nFloor := (1243395476153/288230376151711744)
  eFloor := (305011105203/72057594037927936)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=934719,width:=186943,den:=2147483648,localDen:=1947111321950560360698936123457536,lowerC:=4510217822053704616567111680,s:=[1947102470939186715530908693168128,-3540370105697532780497338368,-354026075339866383027535872],L:=[4510217822056991797389975885,1804076237108414481006854144,180405583164359118673674240,-253768831803072708608,-12646107753656352768],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor516Source.source.poly i) 934719 186943 2147483648
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor516Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((25/13) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (25/13) 4 4 WideAnchor516Source.data
    WideAnchor516Source.path_checked WideAnchor516Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor516Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((25/13) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (25/13) 4 4 WideAnchor516Source.data
    WideAnchor516Source.path_swapped WideAnchor516Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor516Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor516Cell064
