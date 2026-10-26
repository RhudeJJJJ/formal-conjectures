/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor546Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor546Cell033
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (420027/274877906944)
  b := (15751/8589934592)
  s := [(2199023031577/2199023255552),(-179179/4398046511104),(-8959/2199023255552)]
  L := [(7820444964421/147573952589676412928),(9384488288519/442721857769029238784),(469221983671/221360928884514619392),(-4949/27670116110564327424),(-115/13835058055282163712)]
  c := (1955111241105/36893488147419103232)
  R := (-41882746319571/5000000000000)
  total := (-1265649301/500000000000000)
  k := 25
  n := 32
  sFloor := (549755733257/1099511627776)
  nFloor := (753750541225/4722366482869645213696)
  eFloor := (724344877541/4722366482869645213696)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=420027,width:=84005,den:=274877906944,localDen:=442721857769029238784,lowerC:=23461334893260,s:=[442721812676905795584,-18036748713984,-1803684937728],L:=[23461334893263,9384488288519,938443967342,-79184,-3680],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor546Source.source.poly i) 420027 84005 274877906944
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor546Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 24) (CoreQuotient.fused G u 5 24) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 24 WideAnchor546Source.data
    WideAnchor546Source.path_checked WideAnchor546Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor546Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 24 5) (CoreQuotient.fused G u 24 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 24 5 WideAnchor546Source.data
    WideAnchor546Source.path_swapped WideAnchor546Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor546Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor546Cell033
