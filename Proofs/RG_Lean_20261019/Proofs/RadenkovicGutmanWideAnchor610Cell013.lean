/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor610Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor610Cell013
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1402375/35184372088832)
  b := (841425/17592186044416)
  s := [(4398046511103/4398046511104)]
  L := [(382195011712319731046358847/21778071482940061661655974875633165533184),(6517581341107/928455029464035206174343168),(325879067215/464227514732017603087171584),(-25/58028439341502200385896448),(5/29014219670751100192948224)]
  c := (1357829446079/77371252455336267181195264)
  R := (-1583687449148327/100000000000000)
  total := (-1254977/10000000000000)
  k := 46
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (465793911173/19342813113834066795298816)
  eFloor := (1028787194429/19342813113834066795298816)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1402375,width:=280475,den:=35184372088832,localDen:=65334214448820184984967924626899496599552,lowerC:=1146585035136388385810153472,s:=[65334214448805329704496500063600707108864],L:=[1146585035136959193139076541,458634014049474730994434048,45863401427416213115371520,-28147497671065600,11258999068426240],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor610Source.source.poly i) 1402375 280475 35184372088832
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor610Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 8) (CoreQuotient.fused G u 6 8) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 6 8 WideAnchor610Source.data
    WideAnchor610Source.path_checked WideAnchor610Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor610Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 6) (CoreQuotient.fused G u 8 6) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 8 6 WideAnchor610Source.data
    WideAnchor610Source.path_swapped WideAnchor610Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor610Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor610Cell013
