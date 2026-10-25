/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor377Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor377Cell008
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (4403/274877906944)
  b := (1352601/70368744177664)
  s := [(4398046511103/4398046511104)]
  L := [(120173606498418120056276413/10889035741470030830827987437816582766592),(341553023453/77371252455336267181195264),(51232817147/116056878683004400771792896),(3/19342813113834066795298816),(-1/14507109835375550096474112)]
  c := (853884831275/77371252455336267181195264)
  R := (-803439884112657/50000000000000)
  total := (-1023553/20000000000000)
  k := 47
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (437740029913/77371252455336267181195264)
  eFloor := (1480110233357/154742504910672534362390528)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1127168,width:=225433,den:=70368744177664,localDen:=32667107224410092492483962313449748299776,lowerC:=360520819495069579581849600,s:=[32667107224402664852248250031800353554432],L:=[360520819495254360168829239,144207943982830976344522752,14420756013273122374418432,5066549580791808,-2251799813685248],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor377Source.source.poly i) 1127168 225433 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor377Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 14) (CoreQuotient.fused G u 2 14) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 2 14 WideAnchor377Source.data
    WideAnchor377Source.path_checked WideAnchor377Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor377Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 2) (CoreQuotient.fused G u 14 2) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 14 2 WideAnchor377Source.data
    WideAnchor377Source.path_swapped WideAnchor377Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor377Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor377Cell008
