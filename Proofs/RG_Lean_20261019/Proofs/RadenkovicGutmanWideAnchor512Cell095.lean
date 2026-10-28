/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor512Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor512Cell095
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (260013/2097152)
  b := (624031/4194304)
  s := [(138256632907/274877906944),(-660326883917/17592186044416),(17226379473/8796093022208)]
  L := [(1792426528577065029451/4722366482869645213696),(2848203962623/52776558133248),(-44911996475/26388279066624),(312927263/3298534883328),(-21858193/1649267441664)]
  c := (1669327289403/4398046511104)
  R := (-24218493575783/50000000000000)
  total := (-11184578304047/1000000000000000)
  k := 2
  n := 32
  sFloor := (2055637595269/8796093022208)
  nFloor := (1174977561723/17179869184)
  eFloor := (1023704750027/17179869184)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=520026,width:=104005,den:=4194304,localDen:=14167099448608935641088,lowerC:=5377279585729659273216,s:=[7125692601487708913664,-531765444579956883456,27745026174382768128],L:=[5377279585731195088353,764558929487711961088,-24111944507274035200,1344012360611790848,-187760448169312256],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor512Source.source.poly i) 520026 104005 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor512Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 42) (CoreQuotient.fused G u 4 42) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 42 WideAnchor512Source.data
    WideAnchor512Source.path_checked WideAnchor512Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor512Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 42 4) (CoreQuotient.fused G u 42 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 42 4 WideAnchor512Source.data
    WideAnchor512Source.path_swapped WideAnchor512Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor512Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor512Cell095
