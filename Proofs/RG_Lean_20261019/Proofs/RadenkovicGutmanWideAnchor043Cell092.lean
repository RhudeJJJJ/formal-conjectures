/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor043Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor043Cell092
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1203765/16777216)
  b := (722259/8388608)
  s := [(2738562788473/4398046511104),(-578132418725/8796093022208),(28318307803/4398046511104)]
  L := [(233684610739843622733/1180591620717411303424),(1048991191531/17592186044416),(-6603140095/26388279066624),(-704227325/1099511627776),(127750843/1649267441664)]
  c := (1741086026577/8796093022208)
  R := (-16197985764201/20000000000000)
  total := (-10643150425261/1000000000000000)
  k := 3
  n := 32
  sFloor := (4839482201/17179869184)
  nFloor := (1723489415709/2199023255552)
  eFloor := (2024693364883/2199023255552)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1203765,width:=240753,den:=16777216,localDen:=3541774862152233910272,lowerC:=701053832219137671168,s:=[2205382052725143896064,-232786859173242470400,22804913604739989504],L:=[701053832219530868199,211189821628955492352,-886258461216604160,-2268474997368422400,274342846360715264],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor043Source.source.poly i) 1203765 240753 16777216
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor043Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 22) (CoreQuotient.fused G u 10 22) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 22 WideAnchor043Source.data
    WideAnchor043Source.path_checked WideAnchor043Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor043Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 22 10) (CoreQuotient.fused G u 22 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 22 10 WideAnchor043Source.data
    WideAnchor043Source.path_swapped WideAnchor043Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor043Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor043Cell092
