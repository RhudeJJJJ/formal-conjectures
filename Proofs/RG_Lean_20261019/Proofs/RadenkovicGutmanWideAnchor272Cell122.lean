/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor272Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor272Cell122
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (558091/32768)
  b := (669709/32768)
  s := [(1804039708069/18014398509481984),(-513996706607/9007199254740992),(271312010739/18014398509481984)]
  L := [(594209803598984922339/590295810358705651712),(-34131361163/13194139533312),(1647982641/2199023255552),(-148175059/824633720832),(3779147/137438953472)]
  c := (1104614385953/1099511627776)
  R := (115754890183/50000000000000)
  total := (188437948403/20000000000000)
  k := 0
  n := 32
  sFloor := (523679152797/18014398509481984)
  nFloor := 320956896210340617434238020568457204625698339740453969369387966241538329433527358491661995521184846073636215125342835420642148352
  eFloor := 318778927820865454702387445584081030794624819003951057939865694791861045074470547521068701260856621472499194488226308820662484992
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=558091,width:=111618,den:=32768,localDen:=1770887431076116955136,lowerC:=1779105998384721297408,s:=[177344319462014976,-101055864492589056,26671055903686656],L:=[1782629410796954767017,-4581033748845297664,1327130915150757888,-318203516243935232,48693938315329536],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor272Source.source.poly i) 558091 111618 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor272Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 48) (CoreQuotient.fused G u 0 48) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 48 WideAnchor272Source.data
    WideAnchor272Source.path_checked WideAnchor272Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor272Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 48 0) (CoreQuotient.fused G u 48 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 48 0 WideAnchor272Source.data
    WideAnchor272Source.path_swapped WideAnchor272Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor272Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor272Cell122
