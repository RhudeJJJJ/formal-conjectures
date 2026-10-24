/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor005Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor005Cell010
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (679931/70368744177664)
  b := (186981/17592186044416)
  s := [(2199023255549/2199023255552),(1/4398046511104),(-1/2199023255552)]
  L := [(1757461860705887333354847695/2722258935367507707706996859454145691648),(936562441445/7253554917687775048237056),(23414026579/3626777458843887524118528),(1/113336795588871485128704),(-1/226673591177742970257408)]
  c := (390234924531/604462909807314587353088)
  R := (-1403430624946281/100000000000000)
  total := (-6756859/500000000000000)
  k := 41
  n := 32
  sFloor := (549755813887/1099511627776)
  nFloor := (406320467243/77371252455336267181195264)
  eFloor := (777637797969/154742504910672534362390528)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=679931,width:=67993,den:=70368744177664,localDen:=8166776806102523123120990578362437074944,lowerC:=5272385582114295685608112128,s:=[8166776806091381662767422155888344956928,1856910058928070412348686336,-3713820117856140824697372672],L:=[5272385582117662000064543085,1054475565575225994830151680,52723700688213644612206592,72057594037927936,-36028797018963968],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor005Source.source.poly i) 679931 67993 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor005Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 14) (CoreQuotient.fused G u 9 14) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 14 SymbolicAnchor005Source.data
    SymbolicAnchor005Source.path_checked SymbolicAnchor005Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor005Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 9) (CoreQuotient.fused G u 14 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 14 9 SymbolicAnchor005Source.data
    SymbolicAnchor005Source.path_swapped SymbolicAnchor005Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor005Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor005Cell010
