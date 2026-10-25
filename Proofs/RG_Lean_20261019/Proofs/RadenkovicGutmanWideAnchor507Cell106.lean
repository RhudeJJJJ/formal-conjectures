/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor507Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor507Cell106
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (241489/262144)
  b := (1159147/1048576)
  s := [(1930948183713/17592186044416),(-120155898349/4398046511104),(32147993203/8796093022208)]
  L := [(663398711121399498227/590295810358705651712),(340970716373/6597069766656),(-14865290575/1099511627776),(678843805/412316860416),(-8148685/68719476736)]
  c := (308919097819/274877906944)
  R := (2918809973239/50000000000000)
  total := (12514399344087/1000000000000000)
  k := 0
  n := 32
  sFloor := (1514620576723/35184372088832)
  nFloor := 305808121474056192
  eFloor := 218283356826370048
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=965956,width:=193191,den:=1048576,localDen:=1770887431076116955136,lowerC:=1990196133363644891136,s:=[194375608577764098048,-48381155046605193216,6472245911199154176],L:=[1990196133364198494681,91528629732232921088,-23942226324435763200,2915611941567201280,-209990013482434560],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor507Source.source.poly i) 965956 193191 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor507Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 37) (CoreQuotient.fused G u 4 37) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 37 WideAnchor507Source.data
    WideAnchor507Source.path_checked WideAnchor507Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor507Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 37 4) (CoreQuotient.fused G u 37 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 37 4 WideAnchor507Source.data
    WideAnchor507Source.path_swapped WideAnchor507Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor507Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor507Cell106
