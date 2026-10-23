/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell037
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (557113/4398046511104)
  b := (76603/549755813888)
  s := [(2199023255097/2199023255552),(-181/4398046511104),(-5/2199023255552)]
  L := [(4084275421495/37778931862957161709568),(816850685431/37778931862957161709568),(61263471433/56668397794435742564352),(1/2361183241434822606848),(-1/3541774862152233910272)]
  c := (2042137710747/18889465931478580854784)
  R := (-1147393654444377/100000000000000)
  total := (-144729651/1000000000000000)
  k := 34
  n := 32
  sFloor := (2199023255001/4398046511104)
  nFloor := (1011135064447/1208925819614629174706176)
  eFloor := (241808161767/302231454903657293676544)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell037
