/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor013Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor013Cell059
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (375643/2147483648)
  b := (901543/4294967296)
  s := [(4395948484049/4398046511104),(-838605405/4398046511104),(-41762723/2199023255552)]
  L := [(621960164512131267597059/2475880078570760549798248448),(1809210629541/18014398509481984),(90274672755/9007199254740992),(-4638087/1125899906842624),(-114991/562949953421312)]
  c := (1131338948675/4503599627370496)
  R := (-82892304315847/20000000000000)
  total := (-141719737011/1000000000000000)
  k := 12
  n := 32
  sFloor := (2197513176599/4398046511104)
  nFloor := (1293316153979/576460752303423488)
  eFloor := (614138907525/288230376151711744)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=751286,width:=150257,den:=4294967296,localDen:=2475880078570760549798248448,lowerC:=621960164512018884198400,s:=[2474698994337871647408652288,-472092873683610485391360,-47020645935194310705152],L:=[621960164512131267597059,248656015534533327716352,24814513096948942110720,-10199261174273409024,-505735766358360064],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor013Source.source.poly i) 751286 150257 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor013Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 22) (CoreQuotient.fused G u 9 22) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 22 WideAnchor013Source.data
    WideAnchor013Source.path_checked WideAnchor013Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor013Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 22 9) (CoreQuotient.fused G u 22 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 22 9 WideAnchor013Source.data
    WideAnchor013Source.path_swapped WideAnchor013Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor013Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor013Cell059
