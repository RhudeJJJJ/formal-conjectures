/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor543Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor543Cell008
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (4403/274877906944)
  b := (1352601/70368744177664)
  s := [(4398046510999/4398046511104),(-21/2199023255552),(-1/1099511627776)]
  L := [(2658561046700184050253048371/170141183460469231731687303715884105728),(5667048634711/906694364710971881029632),(94450559165/151115727451828646838272),(11/56668397794435742564352),(-1/9444732965739290427392)]
  c := (1180638274567/75557863725914323419136)
  R := (-622052735093479/50000000000000)
  total := (-39555829/1000000000000000)
  k := 36
  n := 32
  sFloor := (549755813869/1099511627776)
  nFloor := (378237031439/19342813113834066795298816)
  eFloor := (287703756595/19342813113834066795298816)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1127168,width:=225433,den:=70368744177664,localDen:=510423550381407695195061911147652317184,lowerC:=7975683140098929817024462848,s:=[510423550369221722933346449066614063104,-4874388904686184832415301632,-464227514732017603087171584],L:=[7975683140100552150759145113,3190264764946867212970360832,319025627295321739367546880,99079191802150912,-54043195528445952],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor543Source.source.poly i) 1127168 225433 70368744177664
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
end Gebendorfer.RadenkovicGutman.WideAnchor543Cell008
