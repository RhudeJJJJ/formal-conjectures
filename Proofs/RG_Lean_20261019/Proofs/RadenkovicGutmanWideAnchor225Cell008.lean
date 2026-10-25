/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor225Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor225Cell008
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (4403/274877906944)
  b := (1352601/70368744177664)
  s := [(4398046511103/4398046511104)]
  L := [(497285957993/77371252455336267181195264),(2386966245335/928455029464035206174343168),(3729624833/14507109835375550096474112),(-1/7253554917687775048237056),(1/14507109835375550096474112)]
  c := (497285957993/77371252455336267181195264)
  R := (-102119457694931/6250000000000)
  total := (-3252727/62500000000000)
  k := 48
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (927636470537/154742504910672534362390528)
  eFloor := (509257227483/77371252455336267181195264)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1127168,width:=225433,den:=70368744177664,localDen:=928455029464035206174343168,lowerC:=5967431495916,s:=[928455029463824099941810176],L:=[5967431495916,2386966245335,238695989312,-128,64],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor225Source.source.poly i) 1127168 225433 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor225Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 10) (CoreQuotient.fused G u 0 10) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 0 10 WideAnchor225Source.data
    WideAnchor225Source.path_checked WideAnchor225Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor225Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 0) (CoreQuotient.fused G u 10 0) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 10 0 WideAnchor225Source.data
    WideAnchor225Source.path_swapped WideAnchor225Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor225Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor225Cell008
