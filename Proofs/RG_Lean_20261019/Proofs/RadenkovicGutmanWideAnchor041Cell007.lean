/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor041Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor041Cell007
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (939307/70368744177664)
  b := (4403/274877906944)
  s := [(4398046511103/4398046511104)]
  L := [(691368635221615755172141389/87112285931760246646623899502532662132736),(982491831031/309485009821345068724781056),(73686730405/232113757366008801543585792),(3/19342813113834066795298816),(-1/14507109835375550096474112)]
  c := (614058701861/77371252455336267181195264)
  R := (-50730158065617/3125000000000)
  total := (-21544091/500000000000000)
  k := 47
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (512878370193/77371252455336267181195264)
  eFloor := (1813381283911/154742504910672534362390528)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=939307,width:=187861,den:=70368744177664,localDen:=261336857795280739939871698507597986398208,lowerC:=2074105905663607573988769792,s:=[261336857795221318817986000254402828435456],L:=[2074105905664847265516424167,829640595773581484787499008,82963882898527049450782720,40532396646334464,-18014398509481984],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor041Source.source.poly i) 939307 187861 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor041Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 20) (CoreQuotient.fused G u 10 20) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 20 WideAnchor041Source.data
    WideAnchor041Source.path_checked WideAnchor041Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor041Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 20 10) (CoreQuotient.fused G u 20 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 20 10 WideAnchor041Source.data
    WideAnchor041Source.path_swapped WideAnchor041Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor041Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor041Cell007
