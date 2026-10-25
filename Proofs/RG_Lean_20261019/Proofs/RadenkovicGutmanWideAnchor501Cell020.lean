/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor501Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor501Cell020
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1256239/8796093022208)
  b := (753743/4398046511104)
  s := [(4398046510971/4398046511104),(-25/2199023255552),(-1/549755813888)]
  L := [(682174672882508103272131865/42535295865117307932921825928971026432),(969425429853/151115727451828646838272),(48471117161/75557863725914323419136),(-1/2361183241434822606848),(1/4722366482869645213696)]
  c := (75736602865/4722366482869645213696)
  R := (-621401739862243/50000000000000)
  total := (-352310569/1000000000000000)
  k := 36
  n := 32
  sFloor := (68719476733/137438953472)
  nFloor := (255245947163/151115727451828646838272)
  eFloor := (238900152653/151115727451828646838272)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1256239,width:=251247,den:=8796093022208,localDen:=42535295865117307932921825928971026432,lowerC:=682174672882242479540142080,s:=[42535295863831010860851860487083655168,-483570327845851669882470400,-77371252455336267181195264],L:=[682174672882508103272131865,272869000290590856805613568,27286813148063906746335232,-18014398509481984,9007199254740992],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor501Source.source.poly i) 1256239 251247 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor501Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 31) (CoreQuotient.fused G u 4 31) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 31 WideAnchor501Source.data
    WideAnchor501Source.path_checked WideAnchor501Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor501Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 31 4) (CoreQuotient.fused G u 31 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 31 4 WideAnchor501Source.data
    WideAnchor501Source.path_swapped WideAnchor501Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor501Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor501Cell020
