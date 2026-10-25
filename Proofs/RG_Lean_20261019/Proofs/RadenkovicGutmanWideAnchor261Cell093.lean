/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor261Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor261Cell093
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (722259/8388608)
  b := (433355/4194304)
  s := [(83266322573/137438953472),(-208894355123/8796093022208),(5490144405/4398046511104)]
  L := [(86462900919251297791/295147905179352825856),(117414888845/3298534883328),(-14219000119/13194139533312),(162546475/824633720832),(-23262293/824633720832)]
  c := (1288397623885/4398046511104)
  R := (-1227761173353/2000000000000)
  total := (-1007637661879/100000000000000)
  k := 2
  n := 32
  sFloor := (1282782644589/4398046511104)
  nFloor := (513068159359/137438953472)
  eFloor := (859769713979/274877906944)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=722259,width:=144451,den:=8388608,localDen:=885443715538058477568,lowerC:=259388702757664849920,s:=[536439198463832358912,-21027994302475665408,1105312062646517760],L:=[259388702757753893373,31518319228296888320,-954220945201954816,174532948551270400,-24977696916242432],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor261Source.source.poly i) 722259 144451 8388608
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor261Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 38) (CoreQuotient.fused G u 0 38) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 38 WideAnchor261Source.data
    WideAnchor261Source.path_checked WideAnchor261Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor261Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 38 0) (CoreQuotient.fused G u 38 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 38 0 WideAnchor261Source.data
    WideAnchor261Source.path_swapped WideAnchor261Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor261Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor261Cell093
