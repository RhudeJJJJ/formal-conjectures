/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor010Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor010Cell124
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1607301/65536)
  b := (241095/8192)
  s := [(303231657309/9007199254740992),(-2770912140795/144115188075855872),(366348256823/72057594037927936)]
  L := [(1184413624504329902537/1180591620717411303424),(-5599732115/4398046511104),(2455832825/6597069766656),(-24761087/274877906944),(5723083/412316860416)]
  c := (1101996735831/1099511627776)
  R := (112882110811/100000000000000)
  total := (6625282212143/1000000000000000)
  k := 0
  n := 32
  sFloor := (1406745444897/144115188075855872)
  nFloor := 191691126464575563552229135634818594615051847119953784644185644509042590932784831480725504
  eFloor := 191059688296456071116181225466489222439892013770277172457652755229350307035176820048658432
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1607301,width:=321459,den:=65536,localDen:=3541774862152233910272,lowerC:=3549779955519672287232,s:=[119235539360415744,-68097936772177920,18006749519364096],L:=[3553240873512989707611,-4509499931303608320,1318465208477286400,-319044176635232256,49160908634587136],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor010Source.source.poly i) 1607301 321459 65536
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor010Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 19) (CoreQuotient.fused G u 9 19) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 19 WideAnchor010Source.data
    WideAnchor010Source.path_checked WideAnchor010Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor010Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 19 9) (CoreQuotient.fused G u 19 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 19 9 WideAnchor010Source.data
    WideAnchor010Source.path_swapped WideAnchor010Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor010Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor010Cell124
