/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor273Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor273Cell009
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1352601/70368744177664)
  b := (1623121/70368744177664)
  s := [(4398046511103/4398046511104)]
  L := [(3066283588761/618970019642690137449562112),(1226512528723/618970019642690137449562112),(183976743299/928455029464035206174343168),(-1/38685626227668133590597632),(1/58028439341502200385896448)]
  c := (383285448595/77371252455336267181195264)
  R := (-1646930584151557/100000000000000)
  total := (-7869119/125000000000000)
  k := 48
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (794816286261/77371252455336267181195264)
  eFloor := (110064026067/19342813113834066795298816)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1352601,width:=270520,den:=70368744177664,localDen:=1856910058928070412348686336,lowerC:=9198850766280,s:=[1856910058927648199883620352],L:=[9198850766283,3679537586169,367953486598,-48,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor273Source.source.poly i) 1352601 270520 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor273Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 4) (CoreQuotient.fused G u 0 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 4 WideAnchor273Source.data
    WideAnchor273Source.path_checked WideAnchor273Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor273Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 0) (CoreQuotient.fused G u 4 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 0 WideAnchor273Source.data
    WideAnchor273Source.path_swapped WideAnchor273Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor273Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor273Cell009
