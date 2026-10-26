/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor428Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor428Cell074
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1446879/536870912)
  b := (868127/268435456)
  s := [(2198546392657/2199023255552),(-190683387/2199023255552),(-9517155/1099511627776)]
  L := [(78895975482128168589412625/1267650600228229401496703205376),(2690757955169/108086391056891904),(44841522913/18014398509481984),(-323861/6755399441055744),(-2693/1125899906842624)]
  c := (560589622595/9007199254740992)
  R := (-484227280270911/100000000000000)
  total := (-2559478703737/1000000000000000)
  k := 14
  n := 32
  sFloor := (137396042185/274877906944)
  nFloor := (806459514619/9007199254740992)
  eFloor := (351275693151/2251799813685248)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1446879,width:=289375,den:=536870912,localDen:=3802951800684688204490109616128,lowerC:=236687926446244592332308480,s:=[3802127122455096339161413582848,-329764466165354527161581568,-32917597986529730195619840],L:=[236687926446384505768237875,94672629095650829541572608,9466324963205266796445696,-182317534864979525632,-9096145347381559296],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor428Source.source.poly i) 1446879 289375 536870912
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor428Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 2 6 WideAnchor428Source.data
    WideAnchor428Source.path_checked WideAnchor428Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor428Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 6 2 WideAnchor428Source.data
    WideAnchor428Source.path_swapped WideAnchor428Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor428Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor428Cell074
