/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor019Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor019Cell007
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (939307/70368744177664)
  b := (4403/274877906944)
  s := [(4398046511089/4398046511104),(-5/4398046511104),(-1/2199023255552)]
  L := [(1213978749245311916070501935/680564733841876926926749214863536422912),(2587745834977/3626777458843887524118528),(129387016339/1813388729421943762059264),(-19/226673591177742970257408),(5/113336795588871485128704)]
  c := (539114863527/302231454903657293676544)
  R := (-676307139841253/50000000000000)
  total := (-17930021/500000000000000)
  k := 40
  n := 32
  sFloor := (2199023255541/4398046511104)
  nFloor := (1198084537133/77371252455336267181195264)
  eFloor := (35082585979/2417851639229258349412352)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=939307,width:=187861,den:=70368744177664,localDen:=2041694201525630780780247644590609268736,lowerC:=3641936247735139507359449088,s:=[2041694201518667368059267380544301694976,-2321137573660088015435857920,-928455029464035206174343168],L:=[3641936247735935748211505805,1456771397266496279306829824,145676829642725169389633536,-171136785840078848,90071992547409920],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor019Source.source.poly i) 939307 187861 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor019Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 28) (CoreQuotient.fused G u 9 28) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 28 WideAnchor019Source.data
    WideAnchor019Source.path_checked WideAnchor019Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor019Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 28 9) (CoreQuotient.fused G u 28 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 28 9 WideAnchor019Source.data
    WideAnchor019Source.path_swapped WideAnchor019Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor019Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor019Cell007
