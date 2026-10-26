/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor543Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor543Cell062
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1298221/4294967296)
  b := (1557865/4294967296)
  s := [(68145146807/68719476736),(-1815591509/549755813888),(-339020957/1099511627776)]
  L := [(26677652730365641470757/4835703278458516698824704),(3695193943837/1688849860263936),(178501137293/844424930131968),(-153399739/105553116266496),(-3305777/52776558133248)]
  c := (12131591907/2199023255552)
  R := (-51999556144857/20000000000000)
  total := (-151564234441/1000000000000000)
  k := 8
  n := 32
  sFloor := (1086352144937/2199023255552)
  nFloor := (125438042759/18014398509481984)
  eFloor := (381655504813/72057594037927936)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1298221,width:=259644,den:=4294967296,localDen:=14507109835375550096474112,lowerC:=80032958191078308052992,s:=[14385865207833419310956544,-47910335410484979695616,-4473089811374967619584],L:=[80032958191096924412271,31741474282314351509504,3066626187888963878912,-21083099591037943808,-908685062583615488],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor543Source.source.poly i) 1298221 259644 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor543Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 21) (CoreQuotient.fused G u 5 21) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 21 WideAnchor543Source.data
    WideAnchor543Source.path_checked WideAnchor543Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor543Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 21 5) (CoreQuotient.fused G u 21 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 21 5 WideAnchor543Source.data
    WideAnchor543Source.path_swapped WideAnchor543Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor543Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor543Cell062
