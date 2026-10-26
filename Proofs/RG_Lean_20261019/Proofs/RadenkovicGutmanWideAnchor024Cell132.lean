/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor024Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor024Cell132
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (863885/8192)
  b := (518331/4096)
  s := [(245687205107/576460752303423488),(-4507421609303/18446744073709551616),(597851897615/9223372036854775808)]
  L := [(18892845869965112042549/18889465931478580854784),(-313847799/4398046511104),(46608245/2199023255552),(-1431849/274877906944),(111595/137438953472)]
  c := (549824186813/549755813888)
  R := (77726183/1250000000000)
  total := (1573025397259/1000000000000000)
  k := 0
  n := 32
  sFloor := (1137568187337/9223372036854775808)
  nFloor := 2671117482800342885776388115209847844759969827006661869107899955126452882737884461635271977046835485827660630202947744538617457015050939325146719467870588023448884141520742719068045312000
  eFloor := 2670637340367151589992240240020185170059927372289331616689843183849534910407025907753919929437231480627040209920246111520826880569272654599452061838349822749392983155840618908168533049344
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=863885,width:=172777,den:=8192,localDen:=18889465931478580854784,lowerC:=18891815207293035741184,s:=[8050678336946176,-4615599727926272,1224400686315520],L:=[18892845869965112042549,-1347966032626581504,400361775997911040,-98395914044964864,15337500012707840],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor024Source.source.poly i) 863885 172777 8192
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor024Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 33) (CoreQuotient.fused G u 9 33) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 33 WideAnchor024Source.data
    WideAnchor024Source.path_checked WideAnchor024Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor024Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 33 9) (CoreQuotient.fused G u 33 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 33 9 WideAnchor024Source.data
    WideAnchor024Source.path_swapped WideAnchor024Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor024Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor024Cell132
