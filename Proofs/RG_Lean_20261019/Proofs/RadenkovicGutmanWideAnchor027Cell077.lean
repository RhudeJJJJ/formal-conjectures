/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor027Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor027Cell077
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (625051/134217728)
  b := (750061/134217728)
  s := [(3034524951311/4398046511104),(-154466501451/2199023255552),(2579281475/549755813888)]
  L := [(237325842215902943467/1180591620717411303424),(948658509161/17592186044416),(-31953039529/26388279066624),(-394629259/1099511627776),(89307805/1649267441664)]
  c := (884107657581/4398046511104)
  R := (-16043369067549/20000000000000)
  total := (-172640508041/250000000000000)
  k := 3
  n := 32
  sFloor := (171639137513/549755813888)
  nFloor := (655011295687/281474976710656)
  eFloor := (1195518553253/562949953421312)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=625051,width:=125010,den:=134217728,localDen:=3541774862152233910272,lowerC:=711977526647542775808,s:=[2443722267145638248448,-248785714522343079936,16616894373455462400],L:=[711977526647708830401,190990184621184909312,-4288664368276570112,-1271189821087285248,191787050876272640],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor027Source.source.poly i) 625051 125010 134217728
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor027Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 36) (CoreQuotient.fused G u 9 36) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 36 WideAnchor027Source.data
    WideAnchor027Source.path_checked WideAnchor027Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor027Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 36 9) (CoreQuotient.fused G u 36 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 36 9 WideAnchor027Source.data
    WideAnchor027Source.path_swapped WideAnchor027Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor027Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor027Cell077
