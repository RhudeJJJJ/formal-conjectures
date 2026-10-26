/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor517Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor517Cell121
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (116269/8192)
  b := (558091/32768)
  s := [(1543012952141/9007199254740992),(-6991605821461/72057594037927936),(917964752257/36028797018963968)]
  L := [(595840149688448635535/590295810358705651712),(-23841903763/6597069766656),(3393512935/3298534883328),(-99793073/412316860416),(7518797/206158430208)]
  c := (553385135137/549755813888)
  R := (329000056331/100000000000000)
  total := (2226598399421/200000000000000)
  k := 0
  n := 32
  sFloor := (1797106825045/36028797018963968)
  nFloor := 10044173382609311943717027840
  eFloor := 9947302544782550604495978496
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=465076,width:=93015,den:=32768,localDen:=1770887431076116955136,lowerC:=1782578293129466609664,s:=[303368690494537728,-171825704668225536,45119803502936064],L:=[1787520449065345906605,-6400012308529020928,1821878384297246720,-428607984902340608,64585974440525824],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor517Source.source.poly i) 465076 93015 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor517Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 4 4 WideAnchor517Source.data
    WideAnchor517Source.path_checked WideAnchor517Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor517Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 4 4 WideAnchor517Source.data
    WideAnchor517Source.path_swapped WideAnchor517Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor517Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor517Cell121
