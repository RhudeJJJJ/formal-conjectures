/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor268Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor268Cell059
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (375643/2147483648)
  b := (901543/4294967296)
  s := [(4397822735471/4398046511104),(-11187369/549755813888),(-139745/68719476736)]
  L := [(940602479777144025348683387/40564819207303340847894502572032),(1002403857269/108086391056891904),(50099688977/54043195528445952),(-1021657/13510798882111488),(-797/211106232532992)]
  c := (417711412027/18014398509481984)
  R := (-266797278026307/50000000000000)
  total := (-45849059561/250000000000000)
  k := 16
  n := 32
  sFloor := (2198862146419/4398046511104)
  nFloor := (749516003321/288230376151711744)
  eFloor := (822353155981/288230376151711744)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=751286,width:=150257,den:=4294967296,localDen:=121694457621910022543683507716096,lowerC:=2821807439329801381859033088,s:=[121688265724162197513326982856704,-2476446393613823433032859648,-247472664055731963895480320],L:=[2821807439331432076046050161,1128606409517854064541433856,112814470304097472973111296,-9202268169000917663744,-459439219585828519936],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor268Source.source.poly i) 751286 150257 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor268Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 44) (CoreQuotient.fused G u 0 44) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 44 WideAnchor268Source.data
    WideAnchor268Source.path_checked WideAnchor268Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor268Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 44 0) (CoreQuotient.fused G u 44 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 44 0 WideAnchor268Source.data
    WideAnchor268Source.path_swapped WideAnchor268Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor268Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor268Cell059
