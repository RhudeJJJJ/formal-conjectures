/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor514Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor514Cell122
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (558091/32768)
  b := (669709/32768)
  s := [(3595810022903/36028797018963968),(-127800769437/2251799813685248),(269375831285/18014398509481984)]
  L := [(297098216275619762803/295147905179352825856),(-33896488981/13194139533312),(1629086513/2199023255552),(-145723121/824633720832),(3700755/137438953472)]
  c := (269678283/268435456)
  R := (14435019957/6250000000000)
  total := (14679412771/1562500000000)
  k := 0
  n := 32
  sFloor := (2089749374481/72057594037927936)
  nFloor := 320949455159437743162394664192533534789896738326809103077116967886913359421306860371240757975807516469544970325854688342020456448
  eFloor := 318778927820865454702387445584081030794624819003951057939865694791861045074470547521068701260856621472499194488226308820662484992
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=558091,width:=111618,den:=32768,localDen:=885443715538058477568,lowerC:=889543223751500365824,s:=[88370627122864128,-50253307354939392,13240360859320320],L:=[891294648826859288409,-2274754869103427584,655956871470907392,-156469009741512704,23841932543262720],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor514Source.source.poly i) 558091 111618 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor514Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 44) (CoreQuotient.fused G u 4 44) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 44 WideAnchor514Source.data
    WideAnchor514Source.path_checked WideAnchor514Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor514Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 44 4) (CoreQuotient.fused G u 44 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 44 4 WideAnchor514Source.data
    WideAnchor514Source.path_swapped WideAnchor514Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor514Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor514Cell122
