/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor503Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor503Cell128
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (104153/2048)
  b := (249967/4096)
  s := [(4375825770485/1152921504606846976),(-5013814158019/2305843009213693952),(664612553425/1152921504606846976)]
  L := [(9451954456558034093493/9444732965739290427392),(-668088709/2199023255552),(296459443/3298534883328),(-3024333/137438953472),(705209/206158430208)]
  c := (137512082733/137438953472)
  R := (26597194807/100000000000000)
  total := (324273999253/100000000000000)
  k := 0
  n := 32
  sFloor := (633382811225/576460752303423488)
  nFloor := 171718961689811770909849473942581614980882056132109893192285939742899601419191510717781366695904385826436116232783361915196580979493847433216
  eFloor := 171586461813591610255457297699506779492011685516769213916158555186145357345670060799915937247381206223860062005673814067202958319498093920256
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=208306,width:=41661,den:=4096,localDen:=28334198897217871282176,lowerC:=28349275110867902398464,s:=[107540294135439360,-61609748373737472,16333518112972800],L:=[28355863369674102280479,-8608257467945582592,2546567224550752256,-623491743706251264,96923186939035648],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor503Source.source.poly i) 208306 41661 4096
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor503Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 33) (CoreQuotient.fused G u 4 33) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 33 WideAnchor503Source.data
    WideAnchor503Source.path_checked WideAnchor503Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor503Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 33 4) (CoreQuotient.fused G u 33 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 33 4 WideAnchor503Source.data
    WideAnchor503Source.path_swapped WideAnchor503Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor503Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor503Cell128
