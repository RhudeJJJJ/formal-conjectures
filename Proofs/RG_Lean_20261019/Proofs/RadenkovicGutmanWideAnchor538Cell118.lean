/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor538Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor538Cell118
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (538283/65536)
  b := (1291879/131072)
  s := [(239564561133/281474976710656),(-1061388059761/2251799813685248),(273503611401/2251799813685248)]
  L := [(151465627992177500455/147573952589676412928),(-63594353669/6597069766656),(4235869933/1649267441664),(-28904783/51539607552),(511169/6442450944)]
  c := (1120202327501/1099511627776)
  R := (932160603851/100000000000000)
  total := (9049678436411/500000000000000)
  k := 0
  n := 32
  sFloor := (4408718909/17592186044416)
  nFloor := 21968179716911412841730434728579477950963908608
  eFloor := 21367337463467882427710495486371151096800346112
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1076566,width:=215313,den:=131072,localDen:=442721857769029238784,lowerC:=451053033892488413184,s:=[376802473881894912,-208677383653490688,53772998030327808],L:=[454396883976532501365,-4267744831540822016,1137057677021544448,-248290195365953536,35127266203664384],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor538Source.source.poly i) 1076566 215313 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor538Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 16) (CoreQuotient.fused G u 5 16) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 16 WideAnchor538Source.data
    WideAnchor538Source.path_checked WideAnchor538Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor538Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 16 5) (CoreQuotient.fused G u 16 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 16 5 WideAnchor538Source.data
    WideAnchor538Source.path_swapped WideAnchor538Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor538Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor538Cell118
