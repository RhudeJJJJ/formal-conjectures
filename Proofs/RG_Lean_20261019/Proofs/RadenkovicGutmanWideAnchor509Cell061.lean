/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor509Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor509Cell061
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1081851/4294967296)
  b := (1298221/4294967296)
  s := [(4397747390529/4398046511104),(-119629231/4398046511104),(-5976215/2199023255552)]
  L := [(362263608509116626337662757/10141204801825835211973625643008),(772109290441/54043195528445952),(154340668997/108086391056891904),(-253205/1688849860263936),(-50549/6755399441055744)]
  c := (1287018877281/36028797018963968)
  R := (-511987260935001/100000000000000)
  total := (-63301352393/250000000000000)
  k := 15
  n := 32
  sFloor := (1099403952217/2199023255552)
  nFloor := (447499934073/72057594037927936)
  eFloor := (852038183705/144115188075855872)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1081851,width:=216370,den:=4294967296,localDen:=30423614405477505635920876929024,lowerC:=1086790825526532322527019008,s:=[30421545230217178444622488141824,-827538677996880366441332736,-82681281475848096008110080],L:=[1086790825527349879012988271,434658889089923208647278592,43443036211437641538732032,-4561335774593385758720,-227652457563951202304],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor509Source.source.poly i) 1081851 216370 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor509Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 39) (CoreQuotient.fused G u 4 39) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 39 WideAnchor509Source.data
    WideAnchor509Source.path_checked WideAnchor509Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor509Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 39 4) (CoreQuotient.fused G u 39 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 39 4 WideAnchor509Source.data
    WideAnchor509Source.path_swapped WideAnchor509Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor509Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor509Cell061
