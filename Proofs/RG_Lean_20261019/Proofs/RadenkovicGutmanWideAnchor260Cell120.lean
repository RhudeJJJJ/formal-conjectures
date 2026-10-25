/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor260Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor260Cell120
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (775127/65536)
  b := (116269/8192)
  s := [(2663505473515/9007199254740992),(-3015309377785/18014398509481984),(49461563043/1125899906842624)]
  L := [(299112130388508456929/295147905179352825856),(-1415432369/274877906944),(2408529683/1649267441664),(-11763857/34359738368),(5305453/103079215104)]
  c := (554951811271/549755813888)
  R := (470353927329/100000000000000)
  total := (6626041525083/500000000000000)
  k := 0
  n := 32
  sFloor := (775771644483/9007199254740992)
  nFloor := 33885166249519747610740079389870804067587349870047889732108006767906115716927933080666112
  eFloor := 33416305540234330169515397373070040301381609706703068837772562255536605216011014765543424
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=775127,width:=155025,den:=65536,localDen:=885443715538058477568,lowerC:=893812455099340947456,s:=[261833242068418560,-148208486536888320,38898155947032576],L:=[897336391165525370787,-4559426800916103168,1293069527491280896,-303152286538924032,45573494250930176],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor260Source.source.poly i) 775127 155025 65536
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor260Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 37) (CoreQuotient.fused G u 0 37) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 37 WideAnchor260Source.data
    WideAnchor260Source.path_checked WideAnchor260Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor260Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 37 0) (CoreQuotient.fused G u 37 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 37 0 WideAnchor260Source.data
    WideAnchor260Source.path_swapped WideAnchor260Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor260Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor260Cell120
