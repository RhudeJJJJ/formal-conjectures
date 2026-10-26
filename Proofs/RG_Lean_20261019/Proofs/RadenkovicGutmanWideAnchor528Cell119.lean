/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor528Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor528Cell119
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1291879/131072)
  b := (775127/65536)
  s := [(564316020411/1125899906842624),(-5052337377905/18014398509481984),(656633773787/9007199254740992)]
  L := [(300702024225401442861/295147905179352825856),(-92916304669/13194139533312),(4255699597/2199023255552),(-361149263/824633720832),(8783779/137438953472)]
  c := (1114175895865/1099511627776)
  R := (662445916057/100000000000000)
  total := (15493904782461/1000000000000000)
  k := 0
  n := 32
  sFloor := (1322496624061/9007199254740992)
  nFloor := 173877041734815787904221254254592
  eFloor := 170494442288817137967467113480192
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1291879,width:=258375,den:=131072,localDen:=885443715538058477568,lowerC:=897252944012189368320,s:=[443796176563863552,-248332486798786560,64549726498357248],L:=[902106072676204328583,-6235507653414486016,1713570992879566848,-387781068389875712,56589065310437376],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor528Source.source.poly i) 1291879 258375 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor528Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 8) (CoreQuotient.fused G u 4 8) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 8 WideAnchor528Source.data
    WideAnchor528Source.path_checked WideAnchor528Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor528Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 4) (CoreQuotient.fused G u 8 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 8 4 WideAnchor528Source.data
    WideAnchor528Source.path_swapped WideAnchor528Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor528Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor528Cell119
