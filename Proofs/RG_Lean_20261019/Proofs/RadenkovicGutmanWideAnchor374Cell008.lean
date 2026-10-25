/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor374Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor374Cell008
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (4403/274877906944)
  b := (1352601/70368744177664)
  s := [(4398046511103/4398046511104)]
  L := [(4221121192765/618970019642690137449562112),(1688443983237/618970019642690137449562112),(253265923415/928455029464035206174343168),(-1/38685626227668133590597632),(1/58028439341502200385896448)]
  c := (1055280298191/154742504910672534362390528)
  R := (-815474429391443/50000000000000)
  total := (-25974363/500000000000000)
  k := 48
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (881306363477/154742504910672534362390528)
  eFloor := (664621718929/77371252455336267181195264)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1127168,width:=225433,den:=70368744177664,localDen:=1856910058928070412348686336,lowerC:=12663363578292,s:=[1856910058927648199883620352],L:=[12663363578295,5065331949711,506531846830,-48,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor374Source.source.poly i) 1127168 225433 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor374Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 12) (CoreQuotient.fused G u 2 12) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 2 12 WideAnchor374Source.data
    WideAnchor374Source.path_checked WideAnchor374Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor374Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 12 2) (CoreQuotient.fused G u 12 2) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 12 2 WideAnchor374Source.data
    WideAnchor374Source.path_swapped WideAnchor374Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor374Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor374Cell008
