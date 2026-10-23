/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell169
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (38645/1048576)
  b := (85019/2097152)
  s := [(2578987625545/8796093022208),(-39202420551/8796093022208),(4750044043/4398046511104)]
  L := [(2731925991982136396121/4722366482869645213696),(15229348671/2199023255552),(-5073884345/3298534883328),(46491113/274877906944),(-151747/12884901888)]
  c := (1272152174255/2199023255552)
  R := (-27365159770929/100000000000000)
  total := (-499521758519/500000000000000)
  k := 1
  n := 32
  sFloor := (318660661635/2199023255552)
  nFloor := (651061561261/8796093022208)
  eFloor := (615101174215/8796093022208)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 10)
        (CoreQuotient.fused G u 9 10) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 10 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell169
